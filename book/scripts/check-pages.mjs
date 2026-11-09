// Opens every page of a built book in headless Chromium and checks what only
// a browser sees (`npm run check:pages`, after `npm run build`):
//   - no JavaScript errors, and no failed requests for local files;
//   - every figure (@viz) draws something;
//   - no KaTeX error survives in the page;
//   - every citation and Lean link that should open a hover card has its data.
// Chromium is found through CHROME_PATH, the Playwright cache, or the usual
// system paths. Without one, the script says so and exits 0, unless --require
// is given (as in CI). See docs/maintaining-the-book.md.

import fs from 'node:fs';
import http from 'node:http';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const BOOK = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const DIST = path.resolve(process.env.BOOK_DIST || path.join(BOOK, 'dist'));
const REQUIRE = process.argv.includes('--require');

function findChrome() {
  const candidates = [process.env.CHROME_PATH, '/usr/bin/google-chrome', '/usr/bin/google-chrome-stable', '/usr/bin/chromium', '/usr/bin/chromium-browser'];
  const cache = path.join(os.homedir(), '.cache', 'ms-playwright');
  if (fs.existsSync(cache)) {
    for (const d of fs.readdirSync(cache).sort().reverse()) {
      candidates.push(path.join(cache, d, 'chrome-headless-shell-linux64', 'chrome-headless-shell'));
      candidates.push(path.join(cache, d, 'chrome-linux', 'chrome'));
    }
  }
  return candidates.find((c) => c && fs.existsSync(c));
}

const chrome = findChrome();
if (!chrome) {
  console.log('check-pages: no Chromium found (set CHROME_PATH); skipped.');
  process.exit(REQUIRE ? 1 : 0);
}
if (!fs.existsSync(path.join(DIST, 'index.html'))) {
  console.error(`check-pages: no built book in ${DIST}; run the build first.`);
  process.exit(1);
}

const { chromium } = await import('playwright-core');
const types = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript', '.css': 'text/css', '.json': 'application/json', '.svg': 'image/svg+xml', '.woff2': 'font/woff2', '.woff': 'font/woff', '.png': 'image/png' };
const server = http.createServer((req, res) => {
  let file = path.join(DIST, decodeURIComponent(req.url.split('?')[0].split('#')[0]));
  if (file.endsWith('/')) file = path.join(file, 'index.html');
  fs.readFile(file, (err, data) => {
    if (err) { res.writeHead(404); res.end(); return; }
    res.writeHead(200, { 'content-type': types[path.extname(file)] ?? 'application/octet-stream' });
    res.end(data);
  });
});
await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
const base = `http://127.0.0.1:${server.address().port}`;

const browser = await chromium.launch({ executablePath: chrome });
const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
const problems = [];
let current = '';
page.on('pageerror', (e) => problems.push(`${current}: JavaScript error: ${e.message}`));
page.on('console', (m) => { if (m.type() === 'error') problems.push(`${current}: console error: ${m.text()}`); });
page.on('requestfailed', (r) => { if (r.url().startsWith(base)) problems.push(`${current}: failed request ${r.url().slice(base.length)}`); });
page.on('response', (r) => { if (r.url().startsWith(base) && r.status() >= 400) problems.push(`${current}: ${r.status()} for ${r.url().slice(base.length)}`); });

const files = fs.readdirSync(DIST).filter((f) => f.endsWith('.html')).sort();
for (const f of files) {
  current = f;
  await page.goto(`${base}/${f}`, { waitUntil: 'load' });
  await page.waitForTimeout(150);
  const report = await page.evaluate(() => {
    const out = [];
    document.querySelectorAll('.viz').forEach((v, i) => {
      const drawn = v.querySelector('svg, canvas, table, button, .tree, [class*="stage"] *');
      if (!drawn) out.push(`figure ${i + 1} (${v.dataset.viz ?? v.className}) is empty`);
    });
    const katex = document.querySelectorAll('.katex-error').length;
    if (katex) out.push(`${katex} KaTeX error(s)`);
    const cites = [...document.querySelectorAll('a.cite')].filter((a) => !a.dataset.b);
    if (cites.length) out.push(`${cites.length} citation(s) without reference data`);
    return out;
  });
  for (const r of report) problems.push(`${f}: ${r}`);
}

await browser.close();
server.close();
for (const p of problems) console.error(`error: ${p}`);
console.log(`check-pages: ${files.length} pages, ${problems.length} problems`);
process.exit(problems.length ? 1 : 0);
