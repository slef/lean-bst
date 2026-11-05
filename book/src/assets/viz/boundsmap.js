// Map of the sequence bounds of Part II and the relations the library proves
// between them. An arrow A → B means a cost bound in terms of A implies one in
// terms of B: A ≤ c·B plus a startup term, or, for the classical properties, an
// implication between properties of algorithms.
//
// Links are not hard-coded: each node and edge names Lean declarations, and the
// figure borrows the href of a link to that declaration found elsewhere on the
// page (the chapter's table of relations), so the book build checks them.

import { esc, frame, h } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const s = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  parent?.appendChild(e);
  return e;
};
const L = 'RotationBST.';

// Node centres on a 760 × 640 canvas; smaller benchmarks (stronger bounds) on top.
const NODES = [
  { id: 'IB', label: 'IB', name: "Wilber's interleave bound", x: 380, y: 40, def: 'Wilber.interleave', lower: true },
  { id: 'OPT', label: 'OPT', name: 'best BST execution', x: 380, y: 145, def: 'Execution' },
  { id: 'CE', label: 'm(1+H)', name: 'conditional entropy', x: 655, y: 145, def: 'ConditionalEntropy.cost' },
  { id: 'LF', label: 'LF*', name: 'best lazy-finger tree', x: 380, y: 265, def: 'LazyFinger.optimalCost' },
  { id: 'WDF', label: 'WDF*', name: 'weighted dynamic finger', x: 655, y: 265, def: 'WeightedFinger.optimalCostFrom' },
  { id: 'WS', label: 'WS', name: 'working set', x: 115, y: 385, def: 'workingSetSum' },
  { id: 'RF', label: 'RF*', name: 'best static tree', x: 380, y: 385, def: 'StaticTree.cost' },
  { id: 'DF', label: 'DF', name: 'dynamic finger', x: 655, y: 385, def: 'Bounds.dynamicFingerCostFrom' },
  { id: 'SO', label: 'SO', name: 'entropy (static optimality)', x: 380, y: 495, def: 'Bounds.staticCost' },
  { id: 'SF', label: 'SF', name: 'static finger', x: 380, y: 600, def: 'Bounds.fingerCost' },
];

// kind: 'imp' (A → B), 'eq' (both ways), 'not' (no such bound).
const EDGES = [
  { from: 'IB', to: 'OPT', kind: 'imp', label: 'IB ≤ 4r + 2m',
    text: "Wilber's interleave quantity, for any reference tree, is at most 4r + 2m for every execution with r rotations: a lower bound on the optimum.",
    thms: ['Wilber.Results.rotation_lower_bound'] },
  { from: 'OPT', to: 'LF', kind: 'imp', label: '≤ 464·LF* + 16n, strict', strict: true,
    text: 'From every initial tree, some pointer-machine execution costs at most 464·LF* + 16n. The gap is unbounded: on some sequences OPT = o(LF*).',
    thms: ['LazyFinger.Dynamic.Results.optimal', 'LazyFinger.Separation.Results.family'] },
  { from: 'OPT', to: 'CE', kind: 'not', label: 'no bound',
    text: 'No BST execution is bounded by C·m(1+H) + a(n), for any constant C and startup a: there are sequences with H = 0 on which every execution costs more.',
    thms: ['ConditionalEntropy.Results.obstruction'] },
  { from: 'LF', to: 'WDF', kind: 'eq', label: 'within 4×',
    text: 'The best lazy-finger tree and the best weighted dynamic finger bound agree up to a factor 4, after adding the startup term n to both.',
    thms: ['LazyFinger.Results.characterization'] },
  { from: 'LF', to: 'RF', kind: 'imp', label: '≤ 2·RF, strict', strict: true,
    text: 'For every fixed tree, LF* is at most twice its root-finger cost. The gap is unbounded: on some sequences LF* = o(RF*).',
    thms: ['LazyFinger.Results.optimal_root_finger', 'LazyFinger.Sequential.Results.family'] },
  { from: 'LF', to: 'DF', kind: 'imp', label: '≤ 4·DF + n',
    text: 'LF* is at most n plus four times the dynamic finger sum, from any start key.',
    thms: ['LazyFinger.Consequences.Results.dynamic_finger'] },
  { from: 'RF', to: 'SO', kind: 'eq', label: 'within 3×',
    text: 'Every fixed tree costs at least a third of the entropy bound, and some fixed tree costs at most the entropy bound.',
    thms: ['StaticTree.Results.entropy_lower_bound', 'StaticTree.Results.entropy_upper_bound'] },
  { from: 'WS', to: 'SO', kind: 'imp', label: 'property ⇒',
    text: 'Every algorithm with the working-set bound has the static optimality bound (with new constants).',
    thms: ['Bounds.workingSet_implies_staticOptimality'] },
  { from: 'SO', to: 'SF', kind: 'imp', label: 'property ⇒',
    text: 'Every algorithm with the static optimality bound has the static finger bound, for every finger at once.',
    thms: ['Bounds.staticOptimality_implies_staticFinger'] },
];

// Algorithms that meet a bound, drawn as tags next to its node.
const TAGS = [
  { node: 'OPT', text: 'Tango trees: within O(log log n)', href: 'tango.html', x: 132, y: 128 },
  { node: 'LF', text: 'GreedyASS meets it online', href: 'greedy-finger.html', x: 132, y: 248 },
  { node: 'LF', text: 'computed by a DP (static)', href: 'optimal-lazy-finger.html', x: 132, y: 282 },
  { node: 'WS', text: 'splay trees meet it', href: 'analysis.html', x: 115, y: 440 },
  { node: 'CE', text: 'multiple trees (not a BST)', href: 'multiple-trees.html', x: 655, y: 202 },
];

const W = 196, H = 48, TW = 196, TH = 24;

function hrefFor(name) {
  const suffix = `#decl-${L}${name}`;
  for (const a of document.querySelectorAll('a[href]')) {
    if (a.closest('.viz')) continue;
    const href = a.getAttribute('href');
    if (href.endsWith(suffix)) return href;
  }
  return null;
}

// Point where the segment from the centre of a box towards (tx, ty) leaves it.
function clip(n, tx, ty, w = W, hh = H) {
  const dx = tx - n.x, dy = ty - n.y;
  const sx = dx ? (w / 2 + 4) / Math.abs(dx) : Infinity;
  const sy = dy ? (hh / 2 + 4) / Math.abs(dy) : Infinity;
  const k = Math.min(sx, sy);
  return [n.x + dx * k, n.y + dy * k];
}

export default function mount(root) {
  const ui = frame(root, {
    title: 'How the bounds relate',
    help: 'An arrow A → B means a bound in terms of A implies one in terms of B: A ≤ c·B plus a startup term, or, for the classical properties, an implication between properties of algorithms. Double arrows are equivalences up to constants; the dashed red edge is a bound that no BST can meet. Hover over a bound to see what it implies and what implies it; click a bound or an arrow to open its Lean definition or theorem.',
  });
  const byId = Object.fromEntries(NODES.map((n) => [n.id, n]));
  const svg = s('svg', { viewBox: '0 0 760 640', class: 'bounds-map', role: 'img', 'aria-label': 'Map of the bounds and the implications between them' }, ui.stage);
  const defs = s('defs', {}, svg);
  for (const [id, cls] of [['bm-arrow', 'bm-head'], ['bm-arrow-hot', 'bm-head hot']]) {
    const m = s('marker', { id, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    s('path', { d: 'M0,0 L10,5 L0,10 z', class: cls }, m);
  }

  const caption = h('div', { class: 'bm-caption' });
  ui.state.append(caption);
  const idle = 'Hover over a bound or an arrow.';
  caption.textContent = idle;

  const link = (names) => names.map((n) => {
    const href = hrefFor(n);
    return href ? `<a href="${esc(href)}"><code>${esc(n)}</code></a>` : `<code>${esc(n)}</code>`;
  }).join(', ');

  // Edges.
  const edgeEls = [];
  for (const e of EDGES) {
    const a = byId[e.from], b = byId[e.to];
    const [x1, y1] = clip(a, b.x, b.y), [x2, y2] = clip(b, a.x, a.y);
    const g = s('g', { class: `bm-edge ${e.kind}`, tabindex: 0 }, svg);
    s('line', { x1, y1, x2, y2, class: 'bm-hit' }, g);
    const line = s('line', { x1, y1, x2, y2, class: 'bm-line' }, g);
    if (e.kind !== 'not') line.setAttribute('marker-end', 'url(#bm-arrow)');
    if (e.kind === 'eq') line.setAttribute('marker-start', 'url(#bm-arrow)');
    const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
    const horizontal = Math.abs(y2 - y1) < 1;
    const tx = horizontal ? mx : mx + 8, ty = horizontal ? my - 8 : my + 4;
    const label = s('text', { x: tx, y: ty, class: 'bm-label', 'text-anchor': horizontal ? 'middle' : 'start' }, g);
    label.textContent = e.label;
    if (e.kind === 'not') {
      const c = s('text', { x: mx, y: my + 5, class: 'bm-cross', 'text-anchor': 'middle' }, g);
      c.textContent = '✗';
      label.setAttribute('y', my - 10);
      label.setAttribute('text-anchor', 'middle');
      label.setAttribute('x', mx);
    }
    const show = () => {
      clear();
      g.classList.add('hot');
      line.setAttribute('marker-end', e.kind === 'not' ? '' : 'url(#bm-arrow-hot)');
      if (e.kind === 'eq') line.setAttribute('marker-start', 'url(#bm-arrow-hot)');
      caption.innerHTML = `<strong>${esc(a.label)} ${e.kind === 'eq' ? '⇔' : e.kind === 'not' ? '⇏' : '⇒'} ${esc(b.label)}.</strong> ${esc(e.text)} <span class="bm-thm">${link(e.thms)}</span>`;
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => { const href = hrefFor(e.thms[0]); if (href) location.href = href; });
    edgeEls.push({ e, g, line });
  }

  // Algorithm tags.
  for (const t of TAGS) {
    const n = byId[t.node];
    const [x1, y1] = clip({ x: t.x, y: t.y }, n.x, n.y, TW, TH);
    const [x2, y2] = clip(n, t.x, t.y);
    s('line', { x1, y1, x2, y2, class: 'bm-leader' }, svg);
    const a = s('a', { href: t.href, class: 'bm-tag' }, svg);
    s('rect', { x: t.x - TW / 2, y: t.y - TH / 2, width: TW, height: TH, rx: TH / 2 }, a);
    const tx = s('text', { x: t.x, y: t.y + 4, 'text-anchor': 'middle' }, a);
    tx.textContent = t.text;
  }

  // Nodes.
  const nodeEls = new Map();
  for (const n of NODES) {
    const g = s('g', { class: `bm-node${n.lower ? ' lower' : ''}`, tabindex: 0 }, svg);
    s('rect', { x: n.x - W / 2, y: n.y - H / 2, width: W, height: H, rx: 8 }, g);
    const t1 = s('text', { x: n.x, y: n.y - 3, class: 'bm-sym', 'text-anchor': 'middle' }, g);
    t1.textContent = n.label;
    const t2 = s('text', { x: n.x, y: n.y + 15, class: 'bm-name', 'text-anchor': 'middle' }, g);
    t2.textContent = n.name;
    const show = () => {
      clear();
      const down = reach(n.id, false), up = reach(n.id, true);
      for (const [id, el] of nodeEls) {
        el.classList.toggle('focus', id === n.id);
        el.classList.toggle('down', down.has(id) && id !== n.id);
        el.classList.toggle('up', up.has(id) && id !== n.id && !down.has(id));
        el.classList.toggle('dim', id !== n.id && !down.has(id) && !up.has(id));
      }
      for (const { e, g: eg } of edgeEls) {
        const on = e.kind !== 'not' && ((down.has(e.from) && down.has(e.to)) || (up.has(e.from) && up.has(e.to)));
        eg.classList.toggle('dim', !on && !(e.kind === 'not' && (e.from === n.id || e.to === n.id)));
      }
      const names = (set) => [...set].filter((id) => id !== n.id).map((id) => byId[id].label).join(', ') || 'none in this map';
      const what = n.lower ? 'This is a lower bound: every execution costs at least a constant fraction of it.'
        : `A bound in terms of ${n.label} implies bounds in terms of: <strong>${esc(names(down))}</strong>. It follows from a bound in terms of: <strong>${esc(names(up))}</strong>.`;
      caption.innerHTML = `<strong>${esc(n.label)}</strong>, ${esc(n.name)} (${link([n.def])}). ${what}`;
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => { const href = hrefFor(n.def); if (href) location.href = href; });
    nodeEls.set(n.id, g);
  }
  svg.addEventListener('mouseleave', () => { clear(); caption.textContent = idle; });

  function clear() {
    for (const el of nodeEls.values()) el.classList.remove('focus', 'down', 'up', 'dim');
    for (const { e, g, line } of edgeEls) {
      g.classList.remove('hot', 'dim');
      if (e.kind !== 'not') line.setAttribute('marker-end', 'url(#bm-arrow)');
      if (e.kind === 'eq') line.setAttribute('marker-start', 'url(#bm-arrow)');
    }
  }

  // Nodes reachable along implication edges (equivalences both ways), forward or backward.
  function reach(start, backward) {
    const seen = new Set([start]);
    const stack = [start];
    while (stack.length) {
      const u = stack.pop();
      for (const e of EDGES) {
        if (e.kind === 'not') continue;
        const pairs = e.kind === 'eq' ? [[e.from, e.to], [e.to, e.from]] : [backward ? [e.to, e.from] : [e.from, e.to]];
        for (const [p, q] of pairs) if (p === u && !seen.has(q)) { seen.add(q); stack.push(q); }
      }
    }
    return seen;
  }
}
