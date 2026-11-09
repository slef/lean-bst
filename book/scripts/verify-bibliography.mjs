// Checks bibliography entries against the outside world (needs network):
// every DOI must resolve on Crossref or DataCite, and every arXiv id on
// arxiv.org, to a work whose title and first author match the entry; every
// other URL must answer. Run it on new or changed entries before committing:
//
//   npm run verify:bib                 entries that differ from git HEAD
//   npm run verify:bib -- --all        every entry
//   npm run verify:bib -- key1 key2    the given entries
//
// Exits 1 if a link fails or a title does not match. See
// docs/maintaining-the-book.md.

import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const BOOK = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const FILE = process.env.BIB_FILE || path.join(BOOK, 'src', 'bibliography.json');
const entries = JSON.parse(fs.readFileSync(FILE, 'utf8')).entries;
const args = process.argv.slice(2);

let selected;
if (args.includes('--all')) selected = entries;
else if (args.length) selected = entries.filter((e) => args.includes(e.key));
else {
  let old = [];
  try {
    old = JSON.parse(execFileSync('git', ['show', 'HEAD:book/src/bibliography.json'], { cwd: BOOK, encoding: 'utf8', stdio: ['ignore', 'pipe', 'ignore'] })).entries;
  } catch { /* new file: check everything */ }
  const before = new Map(old.map((e) => [e.key, JSON.stringify(e)]));
  selected = entries.filter((e) => before.get(e.key) !== JSON.stringify(e));
}

const norm = (s) => (s ?? '').toLowerCase().normalize('NFKD').replace(/<[^>]+>/g, '').replace(/[^a-z0-9 ]+/g, ' ').replace(/\s+/g, ' ').trim();
const family = (name) => norm(name.split(/\s+/).pop());
function similar(a, b) {
  const x = new Set(norm(a).split(' ')), y = new Set(norm(b).split(' '));
  const common = [...x].filter((w) => y.has(w)).length;
  return common / Math.max(1, Math.min(x.size, y.size));
}

async function get(url, accept) {
  const res = await fetch(url, { headers: { 'user-agent': 'lean-bst-book (mailto:stefan.langerman@ulb.ac.be)', ...(accept ? { accept } : {}) }, redirect: 'follow' });
  return res;
}

async function doiMeta(doi) {
  let res = await get(`https://api.crossref.org/works/${encodeURIComponent(doi)}`);
  if (res.ok) {
    const m = (await res.json()).message;
    return { title: (m.title ?? [])[0] ?? '', authors: (m.author ?? []).map((a) => a.family ?? a.name ?? '') };
  }
  res = await get(`https://api.datacite.org/dois/${encodeURIComponent(doi)}`);
  if (res.ok) {
    const a = (await res.json()).data.attributes;
    return { title: a.titles?.[0]?.title ?? '', authors: (a.creators ?? []).map((c) => c.familyName ?? c.name ?? '') };
  }
  return null;
}

async function arxivMeta(id) {
  const res = await get(`https://export.arxiv.org/api/query?id_list=${encodeURIComponent(id)}`);
  if (!res.ok) return null;
  const xml = await res.text();
  const entry = xml.split('<entry>')[1];
  if (!entry) return null;
  const title = (entry.match(/<title>([\s\S]*?)<\/title>/) ?? [])[1] ?? '';
  const authors = [...entry.matchAll(/<name>([\s\S]*?)<\/name>/g)].map((m) => m[1].trim().split(/\s+/).pop());
  return { title, authors };
}

const problems = [];
const notes = [];
function compare(e, what, meta) {
  if (!meta) { problems.push(`${e.key}: ${what} does not resolve`); return; }
  const s = similar(e.title, meta.title);
  if (s < 0.6) problems.push(`${e.key}: ${what} is "${meta.title}", not "${e.title}"`);
  else if (s < 1) notes.push(`${e.key}: ${what} title differs slightly: "${meta.title}"`);
  const first = family(e.authors[0]);
  if (meta.authors.length && !meta.authors.some((a) => norm(a).includes(first) || first.includes(norm(a)))) {
    problems.push(`${e.key}: ${what} lists authors ${meta.authors.slice(0, 4).join(', ')}, not ${e.authors[0]}`);
  }
}

for (const e of selected) {
  for (const v of [e, ...(e.versions ?? [])]) {
    if (v.doi) compare(e, `doi:${v.doi}`, await doiMeta(v.doi));
    if (v.arxiv) { compare(e, `arXiv:${v.arxiv}`, await arxivMeta(v.arxiv)); await new Promise((r) => setTimeout(r, 3000)); }
    if (v.url) {
      try {
        const res = await get(v.url);
        if (!res.ok) problems.push(`${e.key}: ${v.url} answers ${res.status}`);
      } catch (err) { problems.push(`${e.key}: ${v.url} fails: ${err.message}`); }
    }
  }
  if (!e.doi && !e.arxiv && !e.url) notes.push(`${e.key}: no link (allowed when none can be verified)`);
}

for (const n of notes) console.log(`note: ${n}`);
for (const p of problems) console.error(`error: ${p}`);
console.log(`verify-bibliography: ${selected.length} entries checked, ${problems.length} problems`);
process.exit(problems.length ? 1 : 0);
