// Bibliography: the data in src/bibliography.json, citation syntax, labels and
// formatted references. The build (build.mjs) uses this module; the tests in
// test/bibliography.test.mjs exercise it directly.
//
// Citation syntax in chapters:
//
//   [@key]                 (Sleator and Tarjan 1985)
//   [@a; @b]               (Sleator and Tarjan 1985; Iacono 2001)
//   [@key, Theorem 3]      (Sleator and Tarjan 1985, Theorem 3)
//   [-@key]                (1985), after the authors are already named
//   @key                   Sleator and Tarjan (1985), in running text
//
// In a headline block, `source: @a; @b` lists the papers a result comes from.
// A key is lowercase letters, a four-digit year, then optional lowercase
// letters: `sleator1985`, `demaine2009geometry`.

import { escapeHtml } from './lean-html.mjs';

export const KEY_PATTERN = '[a-z]+\\d{4}[a-z]*';
const KEY = new RegExp(`^${KEY_PATTERN}$`);
const DOI = /^10\.\d{4,9}\/\S+$/;
const ARXIV = /^(\d{4}\.\d{4,5}|[a-z-]+(\.[A-Z]{2})?\/\d{7})$/;
const TYPES = ['article', 'inproceedings', 'incollection', 'book', 'phdthesis', 'mastersthesis', 'techreport', 'preprint', 'misc'];
const FIELDS = ['key', 'type', 'authors', 'title', 'venue', 'volume', 'number', 'pages', 'publisher', 'year', 'doi', 'arxiv', 'url', 'versions', 'note'];
const VERSION_FIELDS = ['label', 'type', 'venue', 'volume', 'number', 'pages', 'publisher', 'year', 'doi', 'arxiv', 'url'];

// An author is written "Given Family", or "Family, Given" when the family name
// has several words ("van Emde Boas, Peter").
export function familyName(author) {
  const comma = author.indexOf(',');
  if (comma >= 0) return author.slice(0, comma).trim();
  const words = author.trim().split(/\s+/);
  return words[words.length - 1];
}
export function displayName(author) {
  const comma = author.indexOf(',');
  return comma >= 0 ? `${author.slice(comma + 1).trim()} ${author.slice(0, comma).trim()}` : author.trim();
}

export function joinNames(names) {
  if (names.length <= 1) return names.join('');
  return `${names.slice(0, -1).join(', ')} and ${names[names.length - 1]}`;
}

function authorsLabel(entry) {
  const fam = entry.authors.map(familyName);
  if (fam.length === 1) return fam[0];
  if (fam.length === 2) return `${fam[0]} and ${fam[1]}`;
  return `${fam[0]} et al.`;
}

// Check the entries, and compute their labels: "Sleator and Tarjan 1985",
// "Demaine et al. 2009". Entries whose labels would coincide get the year
// suffixes a, b, … in bibliography order.
export function loadBibliography(entries) {
  const errors = [];
  const byKey = new Map();
  if (!Array.isArray(entries)) return { errors: ['bibliography: expected an array of entries'], byKey, order: [] };
  for (const [i, e] of entries.entries()) {
    const where = `bibliography entry ${e?.key ?? '#' + i}`;
    if (!e || typeof e !== 'object') { errors.push(`${where}: not an object`); continue; }
    if (typeof e.key !== 'string' || !KEY.test(e.key)) errors.push(`${where}: key must be lowercase letters, a year, then optional letters`);
    if (byKey.has(e.key)) errors.push(`${where}: duplicate key`);
    for (const f of Object.keys(e)) if (!FIELDS.includes(f)) errors.push(`${where}: unknown field ${f}`);
    if (!TYPES.includes(e.type)) errors.push(`${where}: type must be one of ${TYPES.join(', ')}`);
    if (!Array.isArray(e.authors) || !e.authors.length || e.authors.some((a) => typeof a !== 'string' || !a.trim())) errors.push(`${where}: authors must be a non-empty list of names`);
    if (typeof e.title !== 'string' || !e.title.trim()) errors.push(`${where}: missing title`);
    if (!Number.isInteger(e.year)) errors.push(`${where}: year must be an integer`);
    if (e.type !== 'preprint' && !e.venue) errors.push(`${where}: missing venue`);
    if (e.type === 'preprint' && !e.arxiv && !e.url) errors.push(`${where}: a preprint needs arxiv or url`);
    if (e.year && KEY.test(e.key ?? '') && !e.key.includes(String(e.year))) errors.push(`${where}: the key's year differs from ${e.year}`);
    const checkIds = (v, w) => {
      if (v.doi !== undefined && !DOI.test(v.doi)) errors.push(`${w}: malformed doi ${v.doi}`);
      if (v.arxiv !== undefined && !ARXIV.test(v.arxiv)) errors.push(`${w}: malformed arxiv id ${v.arxiv}`);
      if (v.url !== undefined && !/^https?:\/\//.test(v.url)) errors.push(`${w}: url must start with http(s)://`);
    };
    checkIds(e, where);
    for (const v of e.versions ?? []) {
      for (const f of Object.keys(v)) if (!VERSION_FIELDS.includes(f)) errors.push(`${where}: unknown version field ${f}`);
      if (!v.label || !v.venue) errors.push(`${where}: each version needs a label and a venue`);
      checkIds(v, `${where} (${v.label})`);
    }
    byKey.set(e.key, { ...e });
  }
  const order = sortEntries([...byKey.values()]);
  const groups = new Map();
  for (const e of order) {
    const base = `${authorsLabel(e)} ${e.year}`;
    if (!groups.has(base)) groups.set(base, []);
    groups.get(base).push(e);
  }
  for (const [base, group] of groups) {
    group.forEach((e, i) => {
      e.authorsLabel = authorsLabel(e);
      e.yearLabel = group.length > 1 ? `${e.year}${String.fromCharCode(97 + i)}` : String(e.year);
      e.label = group.length > 1 ? `${base}${String.fromCharCode(97 + i)}` : base;
    });
  }
  return { errors, byKey, order };
}

// Bibliography order: family names of the authors, then year, then title.
export function sortEntries(entries) {
  const fold = (s) => s.normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase();
  const sortKey = (e) => e.authors.map((a) => fold(familyName(a))).join(' ');
  return entries.slice().sort((a, b) => sortKey(a).localeCompare(sortKey(b)) || a.year - b.year || fold(a.title).localeCompare(fold(b.title)));
}

// ---------------------------------------------------------------------------
// Parsing

// The inside of a bracketed citation, without the brackets: "@a; -@b, p. 3".
// Returns null when the text is not a citation at all, or a list of items
// {key, suppressAuthor, locator}; malformed items are reported in `errors`.
export function parseCiteGroup(inner) {
  if (!/^\s*-?@/.test(inner)) return null;
  const errors = [];
  const items = [];
  for (const part of inner.split(';')) {
    const m = part.trim().match(new RegExp(`^(-?)@(${KEY_PATTERN})(?:\\s*,\\s*(.+))?$`));
    if (!m) { errors.push(`malformed citation item ${JSON.stringify(part.trim())}`); continue; }
    items.push({ key: m[2], suppressAuthor: m[1] === '-', locator: m[3]?.trim() });
  }
  return { items, errors };
}

// A headline `source:` line: keys separated by semicolons, optionally in
// brackets. Returns the keys, or null if the line holds anything else.
export function parseSourceLine(text) {
  const inner = text.trim().replace(/^\[(.*)\]$/, '$1');
  const parsed = parseCiteGroup(inner);
  if (!parsed || parsed.errors.length || parsed.items.some((i) => i.suppressAuthor || i.locator)) return null;
  return parsed.items.map((i) => i.key);
}

// Every citation key in a Markdown source, outside code spans and fences, for
// checking pages that the build does not render.
export function citedKeys(markdown) {
  const keys = [];
  let fence = null; // null, 'headline' or 'code'
  for (const line of markdown.split('\n')) {
    if (/^\s*```/.test(line)) {
      fence = fence ? null : (line.trim().startsWith('```headline') ? 'headline' : 'code');
      continue;
    }
    if (fence === 'code') continue;
    const text = line.replace(/`[^`]*`/g, '');
    const src = fence === 'headline' && text.match(/^source:\s*(.*)$/);
    if (src) { keys.push(...(parseSourceLine(src[1]) ?? [])); continue; }
    for (const m of text.matchAll(new RegExp(`(^|[^\\w.@])-?@(${KEY_PATTERN})(?![\\w])`, 'g'))) keys.push(m[2]);
  }
  return keys;
}

// ---------------------------------------------------------------------------
// Rendering

const doiUrl = (doi) => `https://doi.org/${doi.split('/').map((s, i) => (i ? encodeURIComponent(s).replace(/%2F/g, '/') : s)).join('/')}`;
const arxivUrl = (id) => `https://arxiv.org/abs/${id}`;

function venueHtml(v) {
  const parts = [];
  if (v.type === 'article') {
    let s = `<em>${escapeHtml(v.venue)}</em>`;
    if (v.volume) s += ` ${escapeHtml(String(v.volume))}`;
    if (v.number) s += `(${escapeHtml(String(v.number))})`;
    if (v.pages) s += `${v.volume ? ':' : ', pages '}${escapeHtml(v.pages)}`;
    parts.push(s);
  } else if (v.type === 'inproceedings' || v.type === 'incollection') {
    let s = `In <em>${escapeHtml(v.venue)}</em>`;
    if (v.volume) s += `, ${escapeHtml(String(v.volume))}`;
    if (v.pages) s += `, pages ${escapeHtml(v.pages)}`;
    parts.push(s);
  } else if (v.venue) {
    let s = escapeHtml(v.venue);
    if (v.pages) s += `, pages ${escapeHtml(v.pages)}`;
    parts.push(s);
  } else if (v.type === 'preprint') {
    parts.push('Preprint');
  }
  if (v.publisher) parts.push(escapeHtml(v.publisher));
  if (v.year) parts.push(String(v.year));
  return parts.join(', ');
}

// The links of an entry or version: DOI, arXiv, then any other URL.
export function linksHtml(v) {
  const links = [];
  if (v.doi) links.push(`<a class="bib-link" href="${escapeHtml(doiUrl(v.doi))}">doi:${escapeHtml(v.doi)}</a>`);
  if (v.arxiv) links.push(`<a class="bib-link" href="${escapeHtml(arxivUrl(v.arxiv))}">arXiv:${escapeHtml(v.arxiv)}</a>`);
  if (v.url) links.push(`<a class="bib-link" href="${escapeHtml(v.url)}">${escapeHtml(v.url.replace(/^https?:\/\/(www\.)?/, '').replace(/\/$/, ''))}</a>`);
  return links.join(' · ');
}

// The full reference as HTML: authors, title, venue, year, links, and the
// other versions of the work.
export function formatReference(entry) {
  const authors = joinNames(entry.authors.map(displayName).map(escapeHtml));
  let title = escapeHtml(entry.title.replace(/\.$/, ''));
  if (entry.type === 'book') title = `<em>${title}</em>`;
  let html = `<span class="bib-authors">${authors}</span>. <span class="bib-title">${title}</span>. ${venueHtml(entry)}.`;
  const links = linksHtml(entry);
  if (links) html += ` <span class="bib-links">${links}</span>`;
  for (const v of entry.versions ?? []) {
    const vl = linksHtml(v);
    html += ` <span class="bib-version">${escapeHtml(v.label)}: ${venueHtml(v)}.${vl ? ` <span class="bib-links">${vl}</span>` : ''}</span>`;
  }
  if (entry.note) html += ` <span class="bib-note">${escapeHtml(entry.note)}</span>`;
  return html;
}

// A citation as HTML. `items` come from parseCiteGroup (or are keys);
// `mode` is 'paren' for [@…], 'narrative' for a bare @key, 'source' for a
// headline source line. `link(entry)` returns the attributes of the anchor:
// {href, attrs}, where attrs is extra HTML such as data-b="3".
export function renderCitation(bib, items, mode, link) {
  const anchor = (entry, text) => {
    const { href, attrs = '' } = link(entry);
    return `<a class="cite" href="${escapeHtml(href)}"${attrs}>${text}</a>`;
  };
  const one = (item) => {
    const entry = bib.byKey.get(item.key);
    const loc = item.locator ? `, ${escapeHtml(item.locator)}` : '';
    if (mode === 'narrative') return anchor(entry, `${escapeHtml(entry.authorsLabel)} (${entry.yearLabel}${loc})`);
    const text = item.suppressAuthor ? entry.yearLabel : `${escapeHtml(entry.authorsLabel)} ${entry.yearLabel}`;
    return anchor(entry, text) + loc;
  };
  const inner = items.map((i) => one(typeof i === 'string' ? { key: i } : i)).join('; ');
  return mode === 'paren' ? `(${inner})` : inner;
}

// markdown-it plugin. Options:
//   bib            the result of loadBibliography
//   link(entry)    as in renderCitation
//   onError(msg)   called for unknown keys and malformed citations
//   onCite(key)    called once per rendered citation of a key
export function citePlugin(md, { bib, link, onError = () => {}, onCite = () => {} }) {
  const known = (key) => {
    if (bib.byKey.has(key)) return true;
    onError(`unknown citation key ${key}`);
    return false;
  };
  md.inline.ruler.before('link', 'cite_group', (state, silent) => {
    const { src, pos } = state;
    if (src.charCodeAt(pos) !== 0x5b) return false;
    if (!(src.startsWith('[@', pos) || src.startsWith('[-@', pos))) return false;
    const end = src.indexOf(']', pos);
    if (end < 0) return false;
    const parsed = parseCiteGroup(src.slice(pos + 1, end));
    if (!parsed) return false;
    if (!silent) {
      for (const e of parsed.errors) onError(e);
      const tok = state.push('cite', '', 0);
      tok.meta = { items: parsed.items.filter((i) => known(i.key)), mode: 'paren', raw: src.slice(pos, end + 1) };
    }
    state.pos = end + 1;
    return true;
  });
  const bare = new RegExp(`^@(${KEY_PATTERN})(?![\\w])`);
  md.inline.ruler.before('link', 'cite_narrative', (state, silent) => {
    const { src, pos } = state;
    if (src.charCodeAt(pos) !== 0x40) return false;
    if (pos > 0 && /[\w.@]/.test(src[pos - 1])) return false;
    const m = src.slice(pos).match(bare);
    if (!m) return false;
    if (!silent) {
      const tok = state.push('cite', '', 0);
      tok.meta = { items: known(m[1]) ? [{ key: m[1] }] : [], mode: 'narrative', raw: m[0] };
    }
    state.pos = pos + m[0].length;
    return true;
  });
  md.renderer.rules.cite = (tokens, idx) => {
    const { items, mode, raw } = tokens[idx].meta;
    if (!items.length) return escapeHtml(raw);
    for (const i of items) onCite(i.key);
    return renderCitation(bib, items, mode, link);
  };
}
