// Render a slice of a Lean source file as HTML, with syntax highlighting from a
// small lexer and semantic links from the compiler's own reference data.
//
// Every identifier the elaborator resolved (recorded in the .ilean file) becomes
// a link carrying the constant's name; the page script turns these into hovers
// showing the signature and docstring Lean itself reports.

const KEYWORDS = new Set([
  'def', 'theorem', 'lemma', 'abbrev', 'instance', 'structure', 'class', 'inductive',
  'where', 'deriving', 'with', 'match', 'fun', 'λ', 'let', 'have', 'show', 'from',
  'if', 'then', 'else', 'do', 'by', 'at', 'in', 'namespace', 'end', 'section',
  'variable', 'open', 'import', 'public', 'private', 'protected', 'noncomputable',
  'partial', 'unsafe', 'mutual', 'module', 'meta', 'universe', 'termination_by',
  'decreasing_by', 'exact', 'return', 'for', 'unless', 'calc', 'extends', 'example',
  'opaque', 'axiom', 'macro', 'syntax', 'notation', 'set_option', 'local', 'scoped',
  'attribute', 'nonrec', 'rec', 'mut', 'classical', 'obtain', 'refine', 'intro',
  'cases', 'induction', 'simp', 'omega', 'rfl', 'exists', 'using',
]);
const SORTS = new Set(['Prop', 'Type', 'Sort']);

// UTF-16 based, like JavaScript strings and the LSP positions in .ilean files.
function lexLine(line, state) {
  // Returns an array of {from, to, cls}; `state.comment` tracks open block comments.
  const out = [];
  let i = 0;
  const n = line.length;
  const push = (from, to, cls) => { if (to > from) out.push({ from, to, cls }); };
  while (i < n) {
    if (state.comment > 0) {
      const start = i;
      while (i < n && state.comment > 0) {
        if (line.startsWith('/-', i)) { state.comment++; i += 2; }
        else if (line.startsWith('-/', i)) { state.comment--; i += 2; }
        else i++;
      }
      push(start, i, state.doc ? 'tk-doc' : 'tk-comment');
      continue;
    }
    const c = line[i];
    if (line.startsWith('--', i)) { push(i, n, 'tk-comment'); break; }
    if (line.startsWith('/-', i)) {
      state.doc = line.startsWith('/--', i) || line.startsWith('/-!', i);
      state.comment = 1;
      const start = i;
      i += 2;
      while (i < n && state.comment > 0) {
        if (line.startsWith('/-', i)) { state.comment++; i += 2; }
        else if (line.startsWith('-/', i)) { state.comment--; i += 2; }
        else i++;
      }
      push(start, i, state.doc ? 'tk-doc' : 'tk-comment');
      continue;
    }
    if (c === '"') {
      const start = i++;
      while (i < n && line[i] !== '"') i += line[i] === '\\' ? 2 : 1;
      push(start, ++i, 'tk-string');
      continue;
    }
    if (c === '@' && line[i + 1] === '[') {
      const start = i;
      const close = line.indexOf(']', i);
      i = close < 0 ? n : close + 1;
      push(start, i, 'tk-attr');
      continue;
    }
    if (/[0-9]/.test(c) && !/[\w.']/.test(line[i - 1] ?? ' ')) {
      const start = i;
      while (i < n && /[0-9]/.test(line[i])) i++;
      push(start, i, 'tk-number');
      continue;
    }
    if (/[\p{L}_«]/u.test(c)) {
      const start = i;
      if (c === '«') { const close = line.indexOf('»', i); i = close < 0 ? n : close + 1; }
      else while (i < n && /[\p{L}\p{N}_'.!?₀-₉ₐ-ₜ]/u.test(line[i])) i++;
      while (line[i - 1] === '.' && i > start + 1) i--;
      const word = line.slice(start, i);
      if (KEYWORDS.has(word)) push(start, i, 'tk-kw');
      else if (SORTS.has(word)) push(start, i, 'tk-sort');
      else push(start, i, 'tk-ident');
      continue;
    }
    if (c === '#' && /[a-z]/.test(line[i + 1] ?? '')) {
      const start = i++;
      while (i < n && /[\w]/.test(line[i])) i++;
      push(start, i, 'tk-kw');
      continue;
    }
    if ('()[]{}⟨⟩'.includes(c)) { push(i, i + 1, 'tk-punct'); i++; continue; }
    if (/[:=|→←↔∀∃λ×∧∨¬≤≥≠<>+\-*/%^·∘∑∈∉⊆∩∪!,;∣↑]/u.test(c)) {
      push(i, i + 1, 'tk-op'); i++; continue;
    }
    i++;
  }
  return out;
}

export function escapeHtml(s) {
  return s.replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}

/**
 * Render lines [startLine, endLine] (zero-based, inclusive) of a module,
 * starting at startCol on the first line and stopping at endCol on the last.
 *
 * linkFor(constant) returns {href, index} or null; anchors maps
 * "line:col" of a definition site to an HTML id.
 */
export function renderLean(module, range, { linkFor, extraRefs = [], anchors = new Map(), highlightLines = new Set(), splitAt = null }) {
  const [startLine, startCol, endLine, endCol] = range;
  const lines = module.source.split('\n');
  // Lex from the top of the file so block comments are tracked correctly.
  const state = { comment: 0, doc: false };
  for (let l = 0; l < startLine; l++) lexLine(lines[l], state);

  const refsByLine = new Map();
  for (const ref of [...module.refs, ...extraRefs]) {
    const [l, c, l2, c2] = ref;
    if (l !== l2 || l < startLine || l > endLine) continue;
    if (!refsByLine.has(l)) refsByLine.set(l, []);
    refsByLine.get(l).push({ from: c, to: c2, constant: ref[4], isDefinition: ref[5] === true });
  }

  const html = [];
  for (let l = startLine; l <= endLine; l++) {
    const full = lines[l] ?? '';
    const from = l === startLine ? startCol : 0;
    const to = l === endLine ? endCol : full.length;
    const tokens = lexLine(full, state);
    // Per-position class and link assignment.
    const cls = new Array(full.length).fill(null);
    for (const t of tokens) for (let i = t.from; i < t.to; i++) cls[i] = t.cls;
    const link = new Array(full.length).fill(null);
    const refs = (refsByLine.get(l) ?? []).sort((a, b) => (b.to - b.from) - (a.to - a.from));
    for (const r of refs) {
      const target = linkFor(r.constant, r.isDefinition);
      if (!target) continue;
      for (let i = r.from; i < r.to; i++) link[i] = { ...target, from: r.from, isDefinition: r.isDefinition };
    }
    let out = '';
    let i = from;
    // With splitAt = [line, col], everything after that position is the proof,
    // hidden until the reader asks for it.
    const splitCol = splitAt && splitAt[0] === l ? splitAt[1] : -1;
    let inProof = false;
    while (i < to) {
      if (i === splitCol && !inProof) {
        out += '<span class="proof-elided"> …</span><span class="proof-body">';
        inProof = true;
      }
      const id = anchors.get(`${l}:${i}`);
      if (id) out += `<span class="anchor" id="${escapeHtml(id)}"></span>`;
      if (link[i]) {
        const start = i;
        const target = link[i];
        while (i < to && link[i] && link[i].from === target.from) i++;
        const text = full.slice(start, i);
        const def = target.isDefinition ? ' def' : '';
        out += `<a class="ref${def}" href="${escapeHtml(target.href)}" data-c="${target.index}">${escapeHtml(text)}</a>`;
        continue;
      }
      const start = i;
      const c = cls[i];
      while (i < to && cls[i] === c && !link[i] && !anchors.has(`${l}:${i + 1}`) && i + 1 !== splitCol) i++;
      if (i === start) i++;
      const text = escapeHtml(full.slice(start, i));
      out += c ? `<span class="${c}">${text}</span>` : text;
    }
    if (splitCol >= 0 && !inProof && to <= splitCol) {
      out += '<span class="proof-elided"> …</span>';
    }
    if (inProof) out += '</span>';
    let mark = highlightLines.has(l) ? ' hl' : '';
    if (splitAt && l > splitAt[0]) mark += ' proof-line';
    html.push(`<span class="line${mark}" data-line="${l + 1}">${out}</span>`);
  }
  // Lines are blocks; no newline characters between them (copying rebuilds them).
  return html.join('');
}
