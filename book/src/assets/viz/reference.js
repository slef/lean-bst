// A fixed reference tree and a request sequence, request by request.
//   mode "interleave": every node shows its region observations (Wilber.labels)
//     and their alternations; the total is Wilber.interleave.
//   mode "paths": the preferred paths (Tango.preferredPaths) after each prefix,
//     with the preference changes made by the current request.
// Options: { tree: Lean syntax | "balanced" | "random" | "left-path" | "right-path",
//            n, seed, requests: [...], mode, step, title }

import * as T from './tree.js';
import * as W from './interleave.js';
import { TreeView } from './render.js';
import { esc, frame, h, label, number, row, select, button } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const PALETTE = 6;

function injectStyle() {
  if (document.getElementById('refviz-style')) return;
  const s = document.createElement('style');
  s.id = 'refviz-style';
  s.textContent = `
.refviz { --p0: var(--series-1); --p1: var(--series-2); --p2: var(--violet); --p3: var(--good); --p4: var(--warn); --p5: var(--bad); }
.refviz .tv-node.switched circle { fill: var(--violet-soft); stroke: var(--violet); stroke-width: 2.6; }
.refviz .tv-node.target circle { fill: var(--target-soft); stroke: var(--target); stroke-width: 2.6; }
.refviz .obs { font-family: var(--mono); font-size: 9.5px; paint-order: stroke; stroke: var(--bg); stroke-width: 3px; stroke-linejoin: round; }
.refviz .obs .L { fill: var(--series-1); }
.refviz .obs .R { fill: var(--series-2); }
.refviz .obs .alt { fill: var(--fg-faint); }
.refviz .tv-edge.unpreferred { stroke: var(--rule); stroke-dasharray: 3 3; }
${[...Array(PALETTE).keys()].map((i) => `.refviz .tv-edge.pp${i} { stroke: var(--p${i}); stroke-width: 4; stroke-linecap: round; }
.refviz .tv-node.pp${i} circle { stroke: var(--p${i}); stroke-width: 2.4; }
.refviz .ppchip.pp${i} { border-color: var(--p${i}); color: var(--p${i}); }`).join('\n')}
.refviz .ppchip { display: inline-block; font-family: var(--mono); font-size: .74rem; border: 1.5px solid var(--rule); border-radius: 5px; padding: 0 .3rem; margin: .1rem .25rem .1rem 0; }
.refviz .reqs { display: flex; flex-wrap: wrap; gap: .2rem; font-family: var(--mono); font-size: .76rem; }
.refviz .reqs span { padding: 0 .25rem; border-radius: 4px; color: var(--fg-faint); cursor: pointer; }
.refviz .reqs span.done { color: var(--fg); }
.refviz .reqs span.now { background: var(--target-soft); color: var(--target); font-weight: 700; }
`;
  document.head.append(s);
}

function makeTree(spec, n, seed) {
  if (spec === 'balanced') return W.balanced(n);
  if (['random', 'left-path', 'right-path', 'zigzag'].includes(spec)) return T.makeTree(spec, n, seed);
  return T.fromLean(spec);
}

export default function mount(root, cfg) {
  injectStyle();
  root.classList.add('refviz');
  const shapes = [['balanced', 'balanced'], ['random', 'random'], ['left-path', 'left path'], ['right-path', 'right path']];
  let spec = cfg.tree ?? 'balanced';
  const custom = !shapes.some(([v]) => v === spec);
  if (custom) shapes.unshift([spec, 'as given']);
  let n = cfg.n ?? 7;
  let seed = cfg.seed ?? 4;
  let tree = makeTree(spec, n, seed);
  if (custom) n = T.size(tree);
  let mode = cfg.mode === 'paths' ? 'paths' : 'interleave';
  let xs = (cfg.requests ?? [0, 6, 1, 5, 2, 4, 3]).slice();
  let j = Math.min(cfg.step ?? xs.length, xs.length);

  const ui = frame(root, {
    title: cfg.title ?? (mode === 'paths' ? 'Preferred paths of a reference tree' : 'The interleave quantity'),
    help: ' ',
  });
  const input = h('input', { type: 'text', class: 'vtext', value: xs.join(' '), 'aria-label': 'request sequence', spellcheck: 'false' });
  input.addEventListener('change', () => {
    const ys = input.value.split(/[\s,]+/).filter(Boolean).map(Number);
    xs = ys.filter((x) => Number.isInteger(x) && x >= 0 && x < n);
    j = xs.length;
    draw();
  });
  const nInput = number(n, { min: 1, max: 31, label: 'number of keys', onChange: (v) => { n = v; rebuild(); } });
  const shapeSel = select(shapes, spec, (v) => { spec = v; rebuild(); });
  const modeSel = select([['interleave', 'interleave'], ['paths', 'preferred paths']], mode, (v) => { mode = v; draw(); });
  const first = button('Start', () => { j = 0; draw(); }, { title: 'before the first request' });
  const prev = button('◀', () => { j = Math.max(0, j - 1); draw(); }, { title: 'previous request' });
  const next = button('▶', () => { j = Math.min(xs.length, j + 1); draw(); }, { title: 'next request' });
  const last = button('End', () => { j = xs.length; draw(); }, { title: 'after the last request' });
  ui.controls.append(label('reference', shapeSel), label('n', nInput), label('view', modeSel));
  const bar2 = h('div', { class: 'viz-bar' }, label('requests', input), first, prev, next, last,
    button('Clear', () => { xs = []; j = 0; draw(); }));
  root.insertBefore(bar2, ui.stage);
  const reqs = h('div', { class: 'reqs' });

  const view = new TreeView(ui.stage, { dy: 60, pad: 30, onNode: (k) => { xs = [...xs.slice(0, j), k]; j = xs.length; draw(); } });
  const overlay = document.createElementNS(SVG, 'g');
  overlay.setAttribute('class', 'obs');
  view.svg.append(overlay);

  function rebuild() {
    if (custom && spec === shapes[0][0]) { tree = makeTree(spec, n, seed); n = T.size(tree); nInput.value = n; }
    else tree = makeTree(spec, n, seed);
    xs = xs.filter((x) => x < n);
    j = Math.min(j, xs.length);
    draw();
  }

  function draw() {
    input.value = xs.join(' ');
    const past = xs.slice(0, j);
    const before = xs.slice(0, Math.max(0, j - 1));
    const x = j > 0 ? xs[j - 1] : null;
    const path = x === null ? [] : W.searchPath(tree, before, x);
    const switched = new Set(path.filter((p) => p.previous !== null && p.previous !== p.next).map((p) => p.key));
    const settled = path.filter((p) => p.previous === null).map((p) => p.key);
    const onPath = new Set(path.map((p) => p.key));
    const classes = new Map();
    const edgeClasses = new Map();
    for (const k of onPath) classes.set(k, 'path');
    for (const k of switched) classes.set(k, 'switched');
    if (x !== null) classes.set(x, 'target');

    const nodes = W.nodeIntervals(tree, past);
    if (mode === 'paths') {
      const paths = W.preferredPaths(tree, past);
      paths.forEach((p, i) => {
        for (let a = 1; a < p.length; a++) edgeClasses.set(p[a], `pp${i % PALETTE}`);
        if (p.length > 1) for (const k of p) if (!classes.has(k)) classes.set(k, `pp${i % PALETTE}`);
      });
      for (const v of nodes) if (!edgeClasses.has(v.key)) edgeClasses.set(v.key, 'unpreferred');
    } else {
      for (const k of onPath) edgeClasses.set(k, 'path');
    }
    view.update(tree, { animate: false, classes, edgeClasses });

    // Observation strings under the nodes (interleave view).
    overlay.replaceChildren();
    if (mode === 'interleave') {
      for (const v of nodes) {
        const p = view.pos.get(v.key);
        if (!p || v.labels.length === 0) continue;
        const t = document.createElementNS(SVG, 'text');
        t.setAttribute('x', p.x);
        t.setAttribute('y', p.y + view.opts.r + 12);
        t.setAttribute('text-anchor', 'middle');
        const shown = v.labels.length > 10 ? v.labels.slice(-10) : v.labels;
        if (shown.length < v.labels.length) t.append(tspan('…', 'alt'));
        for (const b of shown) t.append(tspan(b ? 'L' : 'R', b ? 'L' : 'R'));
        t.append(tspan(` ${W.alternations(v.labels)}`, 'alt'));
        const title = document.createElementNS(SVG, 'title');
        title.textContent = `node ${v.key}: requests in [${v.lo}, ${v.high}) observed as ${v.labels.map((b) => (b ? 'L' : 'R')).join('')}; ${W.alternations(v.labels)} alternation(s)`;
        t.append(title);
        overlay.append(t);
      }
    }

    reqs.replaceChildren(...xs.map((y, i) => {
      const s = h('span', { class: i < j - 1 ? 'done' : i === j - 1 ? 'now' : '' }, String(y));
      s.addEventListener('click', () => { j = i + 1; draw(); });
      return s;
    }));
    first.disabled = prev.disabled = j === 0;
    next.disabled = last.disabled = j === xs.length;

    const keys = (ks) => (ks.length ? esc(ks.join(', ')) : '—');
    const rows = [row(`requests (${j} of ${xs.length} served)`, '')];
    rows[0].querySelector('.vv').append(reqs);
    if (x === null) rows.push(row('current request', '<span class="vnote">none yet: step forward, or click a node to request it</span>'));
    else rows.push(row('current request', `<code>${x}</code>, reference search path ${esc(path.map((p) => p.key).join(' → '))}`));
    if (mode === 'interleave') {
      rows.push(row('switches at this request', x === null ? '—'
        : `${switched.size} <span class="vnote">(nodes ${keys([...switched])}; <code>Tango.changes</code>)</span>`));
      rows.push(row('interleave t (prefix)', `<strong>${W.interleave(tree, past)}</strong> <span class="vnote">after ${j} requests; ${W.interleave(tree, xs)} on the whole sequence</span>`));
    } else {
      const paths = W.preferredPaths(tree, past);
      const chips = paths.map((p, i) => `<span class="ppchip ${p.length > 1 ? `pp${i % PALETTE}` : ''}">${esc(p.join(' '))}</span>`).join('');
      rows.push(row('preferredPaths t past', chips));
      rows.push(row('changes at this request', x === null ? '—'
        : `${switched.size} switch${switched.size === 1 ? '' : 'es'} (nodes ${keys([...switched])}), ${settled.length} first setting${settled.length === 1 ? '' : 's'} (nodes ${keys(settled)})`));
      rows.push(row('totals so far', `interleave ${W.interleave(tree, past)}, preferenceChanges ${W.preferenceChanges(tree, past)}`));
    }
    ui.state.replaceChildren(...rows);
    ui.help.textContent = mode === 'paths'
      ? 'Each node prefers the child on the side of its most recent request (the node itself counts as left). Thick chains are the preferred paths; dashed edges are not preferred. Click a node to request it.'
      : 'Under each node: the sides (L = node or left subtree, R = right subtree) of the requests that fell in its subtree, then the number of alternations. Violet nodes switched side at the current request. Click a node to request it.';
  }

  function tspan(text, cls) {
    const s = document.createElementNS(SVG, 'tspan');
    s.setAttribute('class', cls);
    s.textContent = text;
    return s;
  }

  draw();
}
