// Build the static site in book/dist from book/src and book/build/lean-data.json.
//
// Chapters are Markdown with a few directives, each on its own line:
//
//   @decl Name …        show the Lean source of declarations, exactly as compiled
//   @stmt Name …        the same, with the proof collapsed behind a toggle
//   @viz kind {json}    mount an interactive widget (src/assets/viz)
//   @index              the declaration index (generated)
//   @audit              the audit tables (generated)
//
// and inline [[Name]] or [[Name|text]] for a hyperlinked, hoverable reference.
// Every name must resolve to a constant that Lean exported, or the build fails.

import { copyFileSync, cpSync, existsSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import MarkdownIt from 'markdown-it';
import container from 'markdown-it-container';
import katex from 'katex';
import { escapeHtml, renderLean } from './lean-html.mjs';

const bookDir = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const srcDir = join(bookDir, 'src');
const distDir = resolve(process.env.BOOK_DIST ?? join(bookDir, 'dist'));
const dataPath = join(bookDir, 'build', 'lean-data.json');
if (!existsSync(dataPath)) {
  console.error('Missing build/lean-data.json. Run `npm run extract` first.');
  process.exit(1);
}
const data = JSON.parse(readFileSync(dataPath, 'utf8'));
const config = JSON.parse(readFileSync(join(srcDir, 'book.json'), 'utf8'));
const errors = [];
const fail = (msg) => errors.push(msg);

const STANDARD_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound'];
const LIB = 'RotationBST';
const short = (name) => name.startsWith(LIB + '.') ? name.slice(LIB.length + 1) : name;
const declId = (name) => 'decl-' + name;
const fragment = (id) => '#' + encodeURIComponent(id).replace(/%2E/g, '.');

// ---------------------------------------------------------------------------
// Lean data indexes

const declLoc = new Map(); // name -> {module, range}
for (const [module, m] of Object.entries(data.modules)) {
  for (const [name, range] of Object.entries(m.decls)) declLoc.set(name, { module, range });
}
const consts = data.consts;
const constNames = Object.keys(consts);

function sourceUrl(name) {
  const loc = declLoc.get(name);
  if (!loc) return null;
  const m = data.modules[loc.module];
  const ref = data.dirty || !data.commit ? config.branch : data.commit;
  return `${config.repo}/blob/${ref}/${m.path}#L${loc.range[0] + 1}-L${loc.range[2] + 1}`;
}
function docsUrl(name) {
  const c = consts[name];
  if (!c || !c.module) return null;
  return `https://leanprover-community.github.io/mathlib4_docs/${c.module.replaceAll('.', '/')}.html#${name}`;
}

// ---------------------------------------------------------------------------
// Pass 1: find where each declaration is displayed.

const chapters = config.chapters.map((ch, i) => {
  const text = readFileSync(join(srcDir, 'chapters', ch.file), 'utf8');
  return { ...ch, index: i, text, href: ch.slug === 'index' ? 'index.html' : `${ch.slug}.html` };
});

const home = new Map(); // constant -> {chapter, id}
const displayed = []; // [{name, chapter}]
const DIRECTIVE = /^@(decl|stmt)\s+(.+)$/;

function resolveName(text, where) {
  const name = text.trim();
  if (consts[name]) return name;
  const candidates = constNames.filter((c) => c.endsWith('.' + name));
  if (candidates.length === 1) return candidates[0];
  if (candidates.length > 1) {
    const shown = candidates.filter((c) => home.has(c));
    if (shown.length === 1) return shown[0];
    const lib = candidates.filter((c) => c.startsWith(LIB + '.'));
    const exact = lib.filter((c) => c === `${LIB}.${name}`);
    if (exact.length === 1) return exact[0];
    fail(`${where}: ambiguous name ${name}: ${candidates.slice(0, 6).join(', ')}`);
    return null;
  }
  fail(`${where}: unknown Lean name ${name}`);
  return null;
}

for (const ch of chapters) {
  let inFence = false;
  for (const line of ch.text.split('\n')) {
    if (line.startsWith('```')) inFence = !inFence;
    const m = !inFence && line.match(DIRECTIVE);
    if (!m) continue;
    for (const raw of m[2].trim().split(/\s+/)) {
      const name = resolveName(raw, ch.file);
      if (!name) continue;
      if (!declLoc.has(name)) { fail(`${ch.file}: ${name} has no source range`); continue; }
      if (home.has(name)) continue; // first display is the home
      home.set(name, { chapter: ch, id: declId(name) });
      displayed.push({ name, chapter: ch });
    }
  }
}
// Constructors and fields live inside their parent's block.
for (const { name, chapter } of displayed) {
  const { module, range } = declLoc.get(name);
  for (const d of data.modules[module].defs) {
    if (d[0] >= range[0] && d[0] <= range[2] && !home.has(d[4])) {
      home.set(d[4], { chapter, id: declId(d[4]) });
    }
  }
}
// Where is each module first discussed? (For reading-base links.)
const moduleHome = new Map();
for (const { name, chapter } of displayed) {
  const { module } = declLoc.get(name);
  if (!moduleHome.has(module)) moduleHome.set(module, { chapter, id: declId(name) });
}

// ---------------------------------------------------------------------------
// Rendering helpers

const md = new MarkdownIt({ html: true, typographer: true });
const docMd = new MarkdownIt({ html: false, typographer: false });

const katexMacros = config.katexMacros ?? {};
function tex(src, displayMode, where) {
  try {
    return katex.renderToString(src, { displayMode, throwOnError: true, macros: { ...katexMacros }, strict: 'ignore' });
  } catch (e) {
    fail(`${where}: KaTeX error in ${JSON.stringify(src)}: ${e.message}`);
    return `<code>${escapeHtml(src)}</code>`;
  }
}

class Page {
  constructor(chapter) {
    this.chapter = chapter;
    this.hover = [];
    this.hoverIndex = new Map();
  }
  // Hover/link target for a constant, as seen from this page.
  target(name) {
    let index = this.hoverIndex.get(name);
    const c = consts[name];
    const h = home.get(name);
    const href = h
      ? (h.chapter === this.chapter ? '' : h.chapter.href) + fragment(h.id)
      : (sourceUrl(name) ?? docsUrl(name) ?? '#');
    if (index === undefined) {
      index = this.hover.length;
      this.hoverIndex.set(name, index);
      const entry = { n: short(name), k: c?.kind ?? '', s: c ? c.sig : name, m: c?.module ?? '' };
      if (c?.doc) entry.d = docMd.render(c.doc);
      if (h) entry.b = `${h.chapter.number ? h.chapter.number + ' · ' : ''}${h.chapter.title}`;
      else if (c?.module?.startsWith(LIB)) entry.b = 'library source on GitHub';
      else if (c?.module) entry.b = 'documentation';
      this.hover.push(entry);
    }
    return { href, index };
  }
}

function axiomsBadge(name) {
  const c = consts[name];
  if (!c || !c.axioms) return '';
  const axioms = c.axioms;
  if (axioms.length === 0) {
    return `<span class="badge axioms none" title="Depends on no axioms at all: the kernel checks it constructively.">no axioms</span>`;
  }
  const extra = axioms.filter((a) => !STANDARD_AXIOMS.includes(a));
  const cls = extra.length ? 'axioms bad' : 'axioms std';
  const title = extra.length
    ? `Depends on non-standard axioms: ${extra.join(', ')}`
    : `Depends only on Lean's standard axioms: ${axioms.join(', ')}.`;
  return `<span class="badge ${cls}" title="${escapeHtml(title)}">${extra.length ? '⚠ ' : ''}${escapeHtml(axioms.join(' · '))}</span>`;
}

function readingBase(page, module) {
  const audits = data.modules[module].audits;
  if (!audits.length) return '';
  const parts = audits.map((a) => {
    const links = a.allowed.map((mod) => {
      const h = moduleHome.get(mod);
      const label = escapeHtml(mod.replace(LIB + '.', '').replace(/\.Abstract$/, ''));
      if (!h) return `<code>${label}</code>`;
      const href = (h.chapter === page.chapter ? '' : h.chapter.href) + fragment(h.id);
      return `<a href="${href}"><code>${label}</code></a>`;
    });
    return links.join(', ');
  });
  return `<div class="reading-base" title="Checked by #check_bst_abstract in this file: the statement mentions only definitions from these readable modules, plus Lean, Std and Mathlib.">`
    + `<span class="rb-label">Statement reads only</span> ${parts.join('; ')}</div>`;
}

function statementEnd(source, range) {
  // Position just after the first top-level ":=" of the declaration.
  const lines = source.split('\n');
  for (let l = range[0]; l <= range[2]; l++) {
    const line = lines[l];
    const from = l === range[0] ? range[1] : 0;
    const idx = line.indexOf(':=', from);
    if (idx >= 0 && !line.slice(0, idx).trimStart().startsWith('--')) {
      return [l, idx + 2];
    }
  }
  return null;
}

function renderDecl(page, name, mode) {
  const { module, range } = declLoc.get(name);
  const m = data.modules[module];
  const c = consts[name];
  const h = home.get(name);
  const isHome = h && h.chapter === page.chapter && !page.placed?.has(name);
  page.placed ??= new Set();
  const id = isHome ? declId(name) : null;
  if (isHome) page.placed.add(name);

  const anchors = new Map();
  const extraRefs = [[range[4], range[5], range[6], range[7], name, true]];
  for (const d of m.defs) {
    if (d[0] < range[0] || d[0] > range[2] || d[4] === name) continue;
    extraRefs.push([...d, true]);
    if (isHome) anchors.set(`${d[0]}:${d[1]}`, declId(d[4]));
  }
  const linkFor = (constant) => page.target(constant);
  const opts = { linkFor, extraRefs, anchors };

  let toggle = '';
  const end = mode === 'stmt' ? statementEnd(m.source, range) : null;
  const split = end && (end[0] < range[2] || end[1] < range[3] - 4) ? end : null;
  if (split) toggle = `<button class="proof-toggle" type="button" aria-expanded="false">show proof</button>`;
  const code = renderLean(m, range, { ...opts, splitAt: split });

  const src = sourceUrl(name);
  const fileLabel = `${m.path.replace(LIB + '/', '')}:${range[0] + 1}`;
  const kind = c?.kind ?? 'decl';
  const selfHref = h ? (h.chapter === page.chapter ? '' : h.chapter.href) + fragment(h.id) : '#';
  return `<figure class="decl kind-${kind}"${id ? ` id="${escapeHtml(id)}"` : ''}>`
    + `<figcaption><span class="decl-kind">${kind}</span>`
    + `<a class="decl-name" href="${selfHref}">${escapeHtml(short(name))}</a>`
    + `<span class="decl-meta">${axiomsBadge(name)}`
    + (src ? `<a class="decl-src" href="${escapeHtml(src)}" title="Open the source on GitHub">${escapeHtml(fileLabel)}</a>` : '')
    + `${toggle}<button class="copy" type="button" title="Copy the Lean source">copy</button></span></figcaption>`
    + `<pre class="lean"><code>${code}</code></pre>`
    + (kind === 'theorem' ? readingBase(page, module) : '')
    + `</figure>`;
}

function renderRefInline(page, text, where) {
  // In a Markdown table cell the separator is written `\|`.
  const [nameText, label] = text.split(/\\?\|/);
  const name = resolveName(nameText, where);
  if (!name) return `<code>${escapeHtml(text)}</code>`;
  const t = page.target(name);
  const shown = label ?? short(name).split('.').slice(-2).join('.');
  return `<a class="ref inline" href="${escapeHtml(t.href)}" data-c="${t.index}"><code>${escapeHtml(shown)}</code></a>`;
}

// ---------------------------------------------------------------------------
// markdown-it extensions

let currentPage = null;
let currentWhere = '';

// Inline [[Name]].
md.inline.ruler.before('link', 'leanref', (state, silent) => {
  const { src, pos } = state;
  if (src.charCodeAt(pos) !== 0x5b || src.charCodeAt(pos + 1) !== 0x5b) return false;
  const end = src.indexOf(']]', pos + 2);
  if (end < 0) return false;
  if (!silent) state.push('leanref', '', 0).content = src.slice(pos + 2, end);
  state.pos = end + 2;
  return true;
});
md.renderer.rules.leanref = (tokens, idx) => renderRefInline(currentPage, tokens[idx].content, currentWhere);

// Inline math $…$.
md.inline.ruler.after('escape', 'math_inline', (state, silent) => {
  const { src, pos } = state;
  if (src[pos] !== '$' || src[pos + 1] === '$') return false;
  let end = pos + 1;
  while (end < src.length && (src[end] !== '$' || src[end - 1] === '\\')) end++;
  if (end >= src.length || end === pos + 1) return false;
  const content = src.slice(pos + 1, end);
  if (/^\s|\s$/.test(content)) return false;
  if (!silent) state.push('math_inline', '', 0).content = content;
  state.pos = end + 1;
  return true;
});
md.renderer.rules.math_inline = (tokens, idx) => tex(tokens[idx].content, false, currentWhere);

// Display math $$ … $$ (may span lines).
md.block.ruler.before('fence', 'math_block', (state, startLine, endLine, silent) => {
  const start = state.bMarks[startLine] + state.tShift[startLine];
  const max = state.eMarks[startLine];
  const first = state.src.slice(start, max);
  if (!first.startsWith('$$')) return false;
  if (silent) return true;
  let content = first.slice(2);
  let line = startLine;
  let closed = content.trimEnd().endsWith('$$');
  if (closed) content = content.trimEnd().slice(0, -2);
  while (!closed && ++line < endLine) {
    const text = state.src.slice(state.bMarks[line] + state.tShift[line], state.eMarks[line]);
    if (text.trimEnd().endsWith('$$')) { content += '\n' + text.trimEnd().slice(0, -2); closed = true; }
    else content += '\n' + text;
  }
  state.line = line + 1;
  state.push('math_block', '', 0).content = content;
  return true;
});
md.renderer.rules.math_block = (tokens, idx) => `<div class="math-display">${tex(tokens[idx].content, true, currentWhere)}</div>\n`;

// Directives on their own line.
md.block.ruler.before('paragraph', 'directive', (state, startLine, _endLine, silent) => {
  const line = state.src.slice(state.bMarks[startLine] + state.tShift[startLine], state.eMarks[startLine]);
  const m = line.match(/^@(decl|stmt|viz|index|audit)\b(.*)$/);
  if (!m) return false;
  if (silent) return true;
  const tok = state.push('directive', '', 0);
  tok.meta = { kind: m[1], args: m[2].trim() };
  state.line = startLine + 1;
  return true;
});
md.renderer.rules.directive = (tokens, idx) => {
  const { kind, args } = tokens[idx].meta;
  const page = currentPage;
  if (kind === 'decl' || kind === 'stmt') {
    const names = args.split(/\s+/).map((a) => resolveName(a, currentWhere))
      .filter((n) => n && declLoc.has(n));
    return `<div class="decl-group">${names.map((n) => renderDecl(page, n, kind)).join('')}</div>\n`;
  }
  if (kind === 'viz') {
    const space = args.indexOf(' ');
    const name = space < 0 ? args : args.slice(0, space);
    const json = space < 0 ? '{}' : args.slice(space + 1);
    try { JSON.parse(json); } catch (e) { fail(`${currentWhere}: bad @viz JSON: ${e.message}`); }
    if (!/^[a-z][a-z0-9-]*$/.test(name) || !existsSync(join(srcDir, 'assets', 'viz', `${name}.js`))) {
      fail(`${currentWhere}: unknown figure @viz ${name}`);
    }
    page.usesViz = true;
    return `<div class="viz" data-viz="${escapeHtml(name)}" data-config="${escapeHtml(json)}">`
      + `<div class="viz-loading">Interactive figure (requires JavaScript).</div></div>\n`;
  }
  if (kind === 'index') return renderIndex(page);
  if (kind === 'audit') return renderAudit(page);
  return '';
};

// Callouts: ::: note Title / ::: caveat / ::: lean / ::: details Title
for (const kind of ['note', 'caveat', 'check', 'details', 'aside', 'exercise']) {
  md.use(container, kind, {
    render(tokens, idx) {
      const tok = tokens[idx];
      if (tok.nesting === 1) {
        const title = tok.info.trim().slice(kind.length).trim();
        const defaults = { note: 'Note', caveat: 'Caveat', check: 'Reading the Lean', aside: 'Aside', exercise: 'Try it' };
        const heading = title || defaults[kind] || '';
        if (kind === 'details') return `<details class="callout details"><summary>${md.renderInline(heading)}</summary>\n`;
        return `<div class="callout ${kind}"><div class="callout-title">${md.renderInline(heading)}</div>\n`;
      }
      return kind === 'details' ? '</details>\n' : '</div>\n';
    },
  });
}

// Heading ids and section numbers.
const slugify = (s) => s.toLowerCase().replace(/<[^>]+>/g, '').replace(/[^\p{L}\p{N}]+/gu, '-').replace(/^-|-$/g, '');
md.core.ruler.push('sections', (state) => {
  if (state.inlineMode) return;
  const page = currentPage;
  page.toc = [];
  const counters = [0, 0];
  const used = new Set();
  const tokens = state.tokens;
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.type !== 'heading_open') continue;
    const level = Number(t.tag.slice(1));
    const inline = tokens[i + 1];
    const text = inline.children.filter((c) => c.type === 'text' || c.type === 'code_inline').map((c) => c.content).join('');
    if (level === 1) { page.title = text; continue; }
    let id = slugify(text) || 'section';
    while (used.has(id)) id += '-';
    used.add(id);
    t.attrSet('id', id);
    let number = '';
    if (page.chapter.number && (level === 2 || level === 3)) {
      if (level === 2) { counters[0]++; counters[1] = 0; number = `${page.chapter.number}.${counters[0]}`; }
      else { counters[1]++; number = `${page.chapter.number}.${counters[0]}.${counters[1]}`; }
    }
    t.meta = { number, id };
    if (level <= 3) page.toc.push({ level, id, number, html: md.renderInline(inline.content) });
  }
});
const defaultHeadingOpen = md.renderer.rules.heading_open ?? ((tokens, idx, opts, env, self) => self.renderToken(tokens, idx, opts));
md.renderer.rules.heading_open = (tokens, idx, opts, env, self) => {
  const t = tokens[idx];
  let html = defaultHeadingOpen(tokens, idx, opts, env, self);
  if (t.tag === 'h1' && currentPage.chapter.number) {
    html += `<span class="chapnum">Chapter ${currentPage.chapter.number}</span>`;
  } else if (t.tag === 'h1' && currentPage.chapter.appendix) {
    html += `<span class="chapnum">Appendix ${currentPage.chapter.appendix}</span>`;
  }
  if (t.meta?.number) html += `<a class="secnum" href="#${t.meta.id}">${t.meta.number}</a> `;
  else if (t.meta?.id) html += `<a class="secanchor" href="#${t.meta.id}" aria-hidden="true">#</a>`;
  return html;
};

// ---------------------------------------------------------------------------
// Generated pages

function abstractTheorems() {
  const out = [];
  for (const [module, m] of Object.entries(data.modules)) {
    if (!/\.Abstract$/.test(module) || module.includes('AbstractAudit')) continue;
    for (const name of Object.keys(m.decls)) out.push({ module, name });
  }
  return out.sort((a, b) => a.module.localeCompare(b.module) || a.name.localeCompare(b.name));
}

function renderIndex(page) {
  const rows = displayed
    .slice()
    .sort((a, b) => short(a.name).localeCompare(short(b.name)))
    .map(({ name, chapter }) => {
      const t = page.target(name);
      const c = consts[name];
      return `<tr data-search="${escapeHtml(short(name).toLowerCase())}"><td><a class="ref" href="${t.href}" data-c="${t.index}"><code>${escapeHtml(short(name))}</code></a></td>`
        + `<td><span class="kind-pill kind-${c.kind}">${c.kind}</span></td>`
        + `<td>${chapter.number ? chapter.number + '. ' : ''}${escapeHtml(chapter.title)}</td>`
        + `<td><code class="module">${escapeHtml(c.module.replace(LIB + '.', ''))}</code></td></tr>`;
    });
  return `<div class="index-filter"><input type="search" placeholder="Filter declarations…" aria-label="Filter declarations"></div>`
    + `<table class="decl-index"><thead><tr><th>Declaration</th><th>Kind</th><th>Explained in</th><th>Module</th></tr></thead>`
    + `<tbody>${rows.join('')}</tbody></table>\n`;
}

function renderAudit(page) {
  const all = abstractTheorems();
  const missing = all.filter(({ name }) => !home.has(name));
  const theorems = all.filter(({ name }) => consts[name]?.kind === 'theorem');
  const nonstandard = Object.values(consts).filter((c) => c.axioms && c.axioms.some((a) => !STANDARD_AXIOMS.includes(a)));
  const libCount = Object.values(consts).filter((c) => c.axioms).length;
  let html = `<div class="audit-summary">`
    + `<div><strong>${theorems.length}</strong> theorems in the reading interface</div>`
    + `<div><strong>${all.length - missing.length}/${all.length}</strong> reading-interface declarations shown in this book</div>`
    + `<div><strong>${libCount}</strong> library constants audited; <strong>${nonstandard.length}</strong> use a non-standard axiom</div>`
    + `</div>`;
  html += `<table class="audit"><thead><tr><th>Theorem</th><th>Axioms</th><th>Explained in</th></tr></thead><tbody>`;
  for (const { name } of theorems) {
    const t = page.target(name);
    const h = home.get(name);
    html += `<tr><td><a class="ref" href="${t.href}" data-c="${t.index}"><code>${escapeHtml(short(name))}</code></a></td>`
      + `<td>${axiomsBadge(name)}</td><td>${h ? escapeHtml((h.chapter.number ? h.chapter.number + '. ' : '') + h.chapter.title) : '<em>not shown</em>'}</td></tr>`;
  }
  html += `</tbody></table>`;
  if (missing.length) {
    html += `<p class="audit-missing">Not shown in the book: ${missing.map(({ name }) => {
      const t = page.target(name);
      return `<a class="ref" href="${t.href}" data-c="${t.index}"><code>${escapeHtml(short(name))}</code></a>`;
    }).join(', ')}.</p>`;
  }
  return html + '\n';
}

// ---------------------------------------------------------------------------
// Page template

function sidebar(page) {
  const items = chapters.map((ch) => {
    const active = ch === page.chapter;
    const label = ch.number ?? ch.appendix;
    const num = label ? `<span class="toc-num">${label}</span>` : '';
    let sub = '';
    if (active && page.toc?.length) {
      sub = '<ol class="toc-sections">' + page.toc.filter((t) => t.level === 2)
        .map((t) => `<li><a href="#${t.id}">${t.number ? `<span class="toc-num">${t.number}</span>` : ''}${t.html}</a></li>`).join('') + '</ol>';
    }
    const part = ch.part ? `<li class="toc-part">${escapeHtml(ch.part)}</li>` : '';
    return `${part}<li class="${active ? 'active' : ''}"><a href="${ch.href}">${num}${escapeHtml(ch.title)}</a>${sub}</li>`;
  });
  return `<nav class="sidebar" aria-label="Chapters"><ol class="toc">${items.join('')}</ol>`
    + `<div class="sidebar-foot">${provenance()}</div></nav>`;
}

function provenance() {
  const commit = data.commit ? data.commit.slice(0, 7) : 'unknown';
  return `Lean code extracted from <a href="${config.repo}">${escapeHtml(config.repo.replace('https://github.com/', ''))}</a>`
    + ` @ <code>${commit}</code>${data.dirty ? ' (with local changes)' : ''}, ${escapeHtml(data.toolchain.replace('leanprover/lean4:', 'Lean '))}.`;
}

function layout(page, body) {
  const ch = page.chapter;
  const prev = chapters[ch.index - 1];
  const next = chapters[ch.index + 1];
  const nav = `<nav class="pager">${prev ? `<a class="prev" href="${prev.href}"><span>Previous</span>${escapeHtml(prev.title)}</a>` : '<span></span>'}`
    + `${next ? `<a class="next" href="${next.href}"><span>Next</span>${escapeHtml(next.title)}</a>` : '<span></span>'}</nav>`;
  const title = ch.slug === 'index' ? config.title : `${page.title ?? ch.title} · ${config.title}`;
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>${escapeHtml(title)}</title>
<link rel="stylesheet" href="assets/fonts.css">
<link rel="stylesheet" href="assets/katex/katex.min.css">
<link rel="stylesheet" href="assets/style.css">
<script>document.documentElement.dataset.theme = localStorage.getItem('theme') || (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');</script>
</head>
<body>
<header class="topbar"><button class="menu" type="button" aria-label="Show chapters">☰</button>
<a class="topbar-title" href="index.html">${escapeHtml(config.title)}</a>
<span class="topbar-spacer"></span>
<a class="topbar-link" href="declarations.html">Declarations</a>
<a class="topbar-link" href="${config.repo}">Lean source</a>
<button class="theme" type="button" aria-label="Toggle dark mode">◐</button></header>
<div class="layout">
${sidebar(page)}
<main class="content">
<article>
${body}
</article>
${nav}
</main>
</div>
<div class="hover-card" role="tooltip" hidden></div>
<script type="application/json" id="lean-hover">${JSON.stringify(page.hover).replace(/</g, '\\u003c')}</script>
<script src="assets/book.js" defer></script>
${page.usesViz ? '<script type="module" src="assets/viz/index.js"></script>' : ''}
</body>
</html>
`;
}

// ---------------------------------------------------------------------------
// Pass 2: render

rmSync(distDir, { recursive: true, force: true });
mkdirSync(join(distDir, 'assets'), { recursive: true });

const rendered = new Map();
const sectionNumbers = new Map(); // href -> id -> section number
for (const ch of chapters) {
  const page = new Page(ch);
  currentPage = page;
  currentWhere = ch.file;
  const body = md.render(ch.text);
  rendered.set(ch.href, { page, body });
  sectionNumbers.set(ch.href, new Map((page.toc ?? []).map((t) => [t.id, t.number])));
}

// Cross-references whose text is "Chapter N", "Section N.M" or "Appendix X" are
// renumbered from their target, so reordering chapters never leaves stale numbers.
for (const [href, entry] of rendered) {
  const body = entry.body.replace(/<a href="([\w-]+\.html)?(?:#([^"]*))?">(Chapter|Section|Appendix) [\w.]+<\/a>/g,
    (whole, file, anchor, word) => {
      const target = file ?? href;
      const ch = chapters.find((c) => c.href === target);
      if (!ch) return whole;
      let label = null;
      if (word === 'Chapter' && ch.number) label = `Chapter ${ch.number}`;
      if (word === 'Appendix' && ch.appendix) label = `Appendix ${ch.appendix}`;
      if (word === 'Section' && anchor) {
        const n = sectionNumbers.get(target)?.get(decodeURIComponent(anchor));
        if (n) label = `Section ${n}`;
      }
      if (!label) { fail(`${href}: cannot number cross-reference ${JSON.stringify(whole)}`); return whole; }
      return whole.replace(/>[^<]*<\/a>$/, `>${label}</a>`);
    });
  const html = layout(entry.page, body);
  rendered.set(href, html);
  writeFileSync(join(distDir, href), html);
}

// Internal links: every page.html#anchor must exist.
{
  const ids = new Map();
  for (const [href, html] of rendered) {
    ids.set(href, new Set([...html.matchAll(/\sid="([^"]+)"/g)].map((m) => m[1].replace(/&quot;/g, '"').replace(/&amp;/g, '&'))));
  }
  for (const [href, html] of rendered) {
    for (const m of html.matchAll(/href="([\w-]+\.html)?(?:#([^"]*))?"/g)) {
      const target = m[1] ?? href;
      if (!ids.has(target)) { fail(`${href}: link to missing page ${target}`); continue; }
      if (m[2] !== undefined && m[2] !== '' && !ids.get(target).has(decodeURIComponent(m[2]))) {
        fail(`${href}: link to missing anchor ${target}#${m[2]}`);
      }
    }
  }
}

// Coverage report.
const uncovered = abstractTheorems().filter(({ name }) => !home.has(name));
if (uncovered.length) {
  console.warn(`${uncovered.length} reading-interface declarations are not shown in the book:`);
  for (const { name } of uncovered) console.warn('  ' + short(name));
}

// Assets.
cpSync(join(srcDir, 'assets'), join(distDir, 'assets'), { recursive: true });
const nm = join(bookDir, 'node_modules');
cpSync(join(nm, 'katex', 'dist', 'katex.min.css'), join(distDir, 'assets', 'katex', 'katex.min.css'));
cpSync(join(nm, 'katex', 'dist', 'fonts'), join(distDir, 'assets', 'katex', 'fonts'), { recursive: true });
let fontsCss = '';
const fonts = [
  ['source-serif-4', ['latin-400', 'latin-400-italic', 'latin-600', 'latin-700']],
  ['inter', ['latin-400', 'latin-500', 'latin-600']],
  ['jetbrains-mono', ['latin-400', 'latin-700', 'latin-ext-400', 'greek-400']],
];
mkdirSync(join(distDir, 'assets', 'fonts'), { recursive: true });
for (const [family, variants] of fonts) {
  for (const v of variants) {
    const css = readFileSync(join(nm, '@fontsource', family, `${v}.css`), 'utf8');
    fontsCss += css.replace(/url\(\.\/files\/([^)]+)\)/g, (_, file) => {
      if (file.endsWith('.woff2')) copyFileSync(join(nm, '@fontsource', family, 'files', file), join(distDir, 'assets', 'fonts', file));
      return `url(fonts/${file})`;
    }).replace(/,\s*url\(fonts\/[^)]+\.woff\) format\('woff'\)/g, '') + '\n';
  }
}
writeFileSync(join(distDir, 'assets', 'fonts.css'), fontsCss);
writeFileSync(join(distDir, '.nojekyll'), '');

if (errors.length) {
  console.error(`Build failed with ${errors.length} error(s):`);
  for (const e of errors) console.error('  ' + e);
  process.exit(1);
}
console.log(`Built ${chapters.length} pages into ${distDir} (${displayed.length} declarations shown).`);
