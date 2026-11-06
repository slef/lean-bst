// Maps of the sequence bounds of Part II and the relations between them.
// An arrow A → B means a cost bound in terms of A implies one in terms of B:
// A ≤ c·B plus a startup term, or, for the classical properties, an
// implication between properties of algorithms. An arrow from an algorithm to
// a bound means the algorithm's cost is within that ratio of the bound.
//
// Two maps share the code: `bigo` (constants ignored, equivalent bounds merged
// into one box, algorithms as bubbles) and `detail` (every bound separate,
// equivalent bounds on one row, constants on every arrow).
//
// Links are not hard-coded: each node and edge names Lean declarations, and the
// figure borrows the href of a link to that declaration found elsewhere on the
// page (the chapter's tables), so the book build checks them. Arrows marked
// `todo` are not formalized yet; they point to the roadmap instead.

import { esc, frame, h } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const s = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  parent?.appendChild(e);
  return e;
};
const L = 'RotationBST.';

const B = {
  IB: { sym: 'IB', name: "Wilber's interleave bound", def: 'Wilber.interleave' },
  OPT: { sym: 'OPT', name: 'best BST execution', def: 'Execution' },
  CE: { sym: 'm(1+H)', name: 'conditional entropy', def: 'ConditionalEntropy.cost' },
  LF: { sym: 'LF*', name: 'best lazy-finger tree', def: 'LazyFinger.optimalCost' },
  WDF: { sym: 'WDF*', name: 'weighted dynamic finger', def: 'WeightedFinger.optimalCostFrom' },
  WS: { sym: 'WS', name: 'working set', def: 'workingSetSum' },
  RF: { sym: 'RF*', name: 'best static tree', def: 'StaticTree.cost' },
  SO: { sym: 'SO', name: 'entropy', def: 'Bounds.staticCost' },
  DF: { sym: 'DF', name: 'dynamic finger', def: 'Bounds.dynamicFingerCostFrom' },
  SF: { sym: 'SF', name: 'static finger', def: 'Bounds.fingerCost' },
};

const T = {
  wilber: ['Wilber.Results.rotation_lower_bound'],
  lfOpt: ['LazyFinger.Dynamic.Results.optimal', 'LazyFinger.Separation.Results.family'],
  wsOpt: ['Splay.Results.pointer_workingSet'],
  obstruction: ['ConditionalEntropy.Results.obstruction'],
  charac: ['LazyFinger.Results.characterization'],
  rootFinger: ['LazyFinger.Results.optimal_root_finger', 'LazyFinger.Sequential.Results.family'],
  dynFinger: ['LazyFinger.Consequences.Results.dynamic_finger'],
  entropy: ['StaticTree.Results.entropy_lower_bound', 'StaticTree.Results.entropy_upper_bound'],
  wsSo: ['Bounds.workingSet_implies_staticOptimality'],
  soSf: ['Bounds.staticOptimality_implies_staticFinger'],
};

const TEXT = {
  wilber: "Wilber's interleave quantity, for any reference tree, is at most 4r + 2m for every execution with r rotations: a lower bound on the optimum.",
  lfOpt: 'From every initial tree, some pointer-machine execution costs at most 464·LF* + 16n. The gap is unbounded: on some sequences OPT = o(LF*).',
  wsOpt: 'Splaying is a pointer-machine execution of cost at most 31·WS + 18n(1 + log n), from every initial tree; so the optimum is too.',
  obstruction: 'No BST execution is bounded by C·m(1+H) + a(n), for any constant C and startup a: there are sequences with H = 0 on which every execution costs more.',
  rootFinger: 'For every fixed tree, LF* is at most twice its root-finger cost. The gap is unbounded: on some sequences LF* = o(RF*).',
  dynFinger: 'LF* is at most n plus four times the dynamic finger sum, from any start key.',
  wsSo: 'Every algorithm with the working-set bound has the static optimality bound (with new constants).',
  soSf: 'Every algorithm with the static optimality bound has the static finger bound, for every finger at once.',
  dfSf: 'The dynamic finger sum is at most twice the static finger sum, for every finger f, plus log(|p − f| + 1) for the start key p: a step from x to y costs at most the steps from x to f and from f to y. This is classical, but not formalized yet.',
};

const MAPS = {
  bigo: {
    w: 780, h: 580, bw: 150,
    title: 'How the bounds relate, up to constants',
    nodes: [
      { id: 'IB', x: 430, y: 45, parts: [B.IB], lower: true },
      { id: 'OPT', x: 430, y: 160, parts: [B.OPT] },
      { id: 'CE', x: 660, y: 160, parts: [B.CE] },
      { id: 'WS', x: 120, y: 290, parts: [B.WS] },
      { id: 'LF', x: 430, y: 290, parts: [B.LF, B.WDF], thms: T.charac,
        note: 'The two are within a factor 4 of each other, after adding n to both.' },
      { id: 'RF', x: 270, y: 420, parts: [B.RF, B.SO], thms: T.entropy,
        note: 'Every fixed tree costs at least a third of SO, and some fixed tree costs at most SO.' },
      { id: 'DF', x: 610, y: 420, parts: [B.DF] },
      { id: 'SF', x: 430, y: 540, parts: [B.SF] },
    ],
    algs: [
      { id: 'tango', label: 'Tango trees', x: 215, y: 62, href: 'tango.html' },
      { id: 'multi', label: 'Multiple trees', sub: 'not a BST', x: 660, y: 50, href: 'multiple-trees.html' },
      { id: 'splay', label: 'Splay trees', x: 120, y: 160, href: 'analysis.html' },
      { id: 'combined', label: 'Combined BST', sub: 'Theorem 4.3', x: 640, y: 222, href: 'combined-finger.html' },
      { id: 'greedy', label: 'GreedyASS', x: 690, y: 284, href: 'greedy-finger.html' },
      { id: 'dp', label: 'Optimal tree (DP)', sub: 'static, offline', x: 690, y: 342, href: 'optimal-lazy-finger.html' },
    ],
    edges: [
      { from: 'IB', to: 'OPT', text: TEXT.wilber, thms: T.wilber },
      { from: 'OPT', to: 'LF', label: 'strict', text: TEXT.lfOpt, thms: T.lfOpt },
      { from: 'OPT', to: 'WS', text: TEXT.wsOpt, thms: T.wsOpt },
      { from: 'OPT', to: 'CE', kind: 'not', label: 'no bound', text: TEXT.obstruction, thms: T.obstruction },
      { from: 'LF', to: 'RF', label: 'strict', lab: [330, 350, 'end'], text: TEXT.rootFinger, thms: T.rootFinger },
      { from: 'LF', to: 'DF', text: TEXT.dynFinger, thms: T.dynFinger },
      { from: 'WS', to: 'RF', text: TEXT.wsSo, thms: T.wsSo },
      { from: 'RF', to: 'SF', text: TEXT.soSf, thms: T.soSf },
      { from: 'DF', to: 'SF', todo: true, label: 'not yet formalized', lab: [535, 500, 'start'], text: TEXT.dfSf },
      { from: 'tango', to: 'OPT', kind: 'alg', label: 'O(log log n)', lab: [318, 98, 'start'],
        text: 'Tango trees, an online BST algorithm, cost at most O(log log n) times the cost of any offline execution from the same initial tree, plus O(n log log n).',
        thms: ['Tango.Algorithm.Results.exists_competitive'] },
      { from: 'splay', to: 'OPT', kind: 'alg', todo: true, label: 'O(log log n · log² log log n)', lab: [272, 150, 'middle'],
        text: 'Chmel, Haeupler, Hladík, Koucký, Roeyskoe, Rozhoň, Sladký and Tarjan (2026) prove that splay trees are O(log log n · log² log log n)-competitive.' },
      { from: 'splay', to: 'WS', kind: 'alg',
        text: 'Splaying, from any initial tree, makes at most 10·WS + 6n(1 + log n) rotations: the working-set theorem of Sleator and Tarjan.',
        thms: ['Splay.Results.workingSet'] },
      { from: 'combined', to: 'OPT', kind: 'alg', label: 'O(log log n)', lab: [556, 199, 'start'],
        text: 'One causal program, GreedyASS and Tango combined by ComboBST and then deamortized, costs O(n + min(WDF*, (m + R)·log log n)) for every offline execution with R rotations, with O(log n) worst-case cost per request.',
        thms: ['Geometric.GreedyASS.Combination.Deamortized.Results.combined'] },
      { from: 'combined', to: 'LF', kind: 'alg',
        text: 'The same program costs O(n + WDF*) for the best positive weights, from any start key, so it also meets LF*.',
        thms: ['Geometric.GreedyASS.Combination.Deamortized.Results.combined'] },
      { from: 'greedy', to: 'LF', kind: 'alg',
        text: 'Some online BST algorithm, simulating GreedyASS, costs at most 722280·LF* + 96303n, and at most 2889120·WDF* + 96303n from every start key.',
        thms: ['Geometric.GreedyASS.Performance.Results.bst'] },
      { from: 'dp', to: 'LF', kind: 'alg',
        text: 'A dynamic program computes a static tree whose lazy-finger cost is exactly LF*. It is offline: it reads the whole sequence first.',
        thms: ['OptimalLazyFinger.Work.Results.root_start'] },
      { from: 'multi', to: 'CE', kind: 'alg', label: 'O(log n / log c)', lab: [668, 106, 'start'],
        text: 'Multiple trees with c successors per key, built from the transition counts of the sequence, serve it within 6(1 + log n)/(1 + log c) times m(1+H), in 10nc words. They are not a BST: they follow stored links between trees.',
        thms: ['MultipleTrees.Results.sequence'] },
    ],
  },
  detail: {
    w: 780, h: 580, bw: 150,
    title: 'How the bounds relate, with constants',
    nodes: [
      { id: 'IB', x: 430, y: 45, parts: [B.IB], lower: true },
      { id: 'OPT', x: 430, y: 160, parts: [B.OPT] },
      { id: 'CE', x: 680, y: 160, parts: [B.CE] },
      { id: 'WS', x: 110, y: 290, parts: [B.WS] },
      { id: 'LF', x: 430, y: 290, parts: [B.LF] },
      { id: 'WDF', x: 680, y: 290, parts: [B.WDF] },
      { id: 'SO', x: 190, y: 420, parts: [B.SO] },
      { id: 'RF', x: 430, y: 420, parts: [B.RF] },
      { id: 'DF', x: 680, y: 420, parts: [B.DF] },
      { id: 'SF', x: 430, y: 540, parts: [B.SF] },
    ],
    algs: [],
    edges: [
      { from: 'IB', to: 'OPT', label: 'IB ≤ 4r + 2m', text: TEXT.wilber, thms: T.wilber },
      { from: 'OPT', to: 'LF', label: '464·LF* + 16n, strict', text: TEXT.lfOpt, thms: T.lfOpt },
      { from: 'OPT', to: 'WS', label: '31·WS + 18n(1+log n)', lab: [268, 210, 'end'], text: TEXT.wsOpt, thms: T.wsOpt },
      { from: 'OPT', to: 'CE', kind: 'not', label: 'no bound', text: TEXT.obstruction, thms: T.obstruction },
      { from: 'LF', to: 'WDF', off: -6, label: '4·WDF* + 3n', lab: [570, 279, 'middle'],
        text: 'LF* + n ≤ 4(WDF* + n): the best lazy-finger tree is within a factor 4 of the best weighted dynamic finger bound.', thms: T.charac },
      { from: 'WDF', to: 'LF', off: -6, label: '4·LF* + 3n', lab: [570, 313, 'middle'],
        text: 'WDF* + n ≤ 4(LF* + n): the weighted dynamic finger bound with the best weights is within a factor 4 of the best lazy-finger tree.', thms: T.charac },
      { from: 'LF', to: 'RF', label: '2·RF*, strict', text: TEXT.rootFinger, thms: T.rootFinger },
      { from: 'LF', to: 'DF', label: '4·DF + n', lab: [572, 352, 'start'], text: TEXT.dynFinger, thms: T.dynFinger },
      { from: 'SO', to: 'RF', off: -6, label: '3·RF*', lab: [310, 409, 'middle'],
        text: 'Every fixed tree costs at least a third of the entropy bound: SO ≤ 3·RF_t for every t.', thms: [T.entropy[0]] },
      { from: 'RF', to: 'SO', off: -6, label: '1·SO', lab: [310, 443, 'middle'],
        text: 'Some fixed tree costs at most the entropy bound: RF_t ≤ SO for some t.', thms: [T.entropy[1]] },
      { from: 'WS', to: 'SO', label: 'property ⇒', lab: [140, 360, 'end'], text: TEXT.wsSo, thms: T.wsSo },
      { from: 'SO', to: 'SF', label: 'property ⇒', lab: [300, 490, 'end'], text: TEXT.soSf, thms: T.soSf },
      { from: 'DF', to: 'SF', todo: true, label: '2·SF + log n, not yet formalized', lab: [560, 500, 'start'], text: TEXT.dfSf },
    ],
  },
};

const BH = 48, AW = 136, AH = 34;

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
function clip(n, tx, ty) {
  const dx = tx - n.x, dy = ty - n.y;
  const sx = dx ? (n.w / 2 + 4) / Math.abs(dx) : Infinity;
  const sy = dy ? (n.h / 2 + 4) / Math.abs(dy) : Infinity;
  const k = Math.min(sx, sy);
  return [n.x + dx * k, n.y + dy * k];
}

export default function mount(root, cfg = {}) {
  const key = MAPS[cfg.map] ? cfg.map : 'bigo';
  const map = MAPS[key];
  const bigo = key === 'bigo';
  const roadmap = cfg.roadmap || null;
  const ui = frame(root, {
    title: map.title,
    help: bigo
      ? 'An arrow A → B means a bound in terms of A implies one in terms of B, up to a constant factor and a startup term. Bounds within constant factors of each other share a box. A bubble is an algorithm; its arrow points to a bound it meets, labelled with the ratio when it is not constant. Dashed grey arrows are not formalized yet; the dashed red edge is a bound that no BST can meet. Hover over a bound or an algorithm to see what follows; click to open its Lean definition, theorem or chapter.'
      : 'An arrow A → B is labelled with the bound on A in terms of B that the library proves. Bounds within constant factors of each other are on the same row, with an arrow each way. Dashed grey arrows are not formalized yet; the dashed red edge is a bound that no BST can meet. Hover over a bound to see what it implies and what implies it; click a bound or an arrow to open its Lean definition or theorem.',
  });

  const nodes = [
    ...map.nodes.map((n) => ({ ...n, w: map.bw * n.parts.length + (n.parts.length > 1 ? 10 : 0), h: BH })),
    ...map.algs.map((a) => ({ ...a, alg: true, w: AW, h: AH })),
  ];
  const byId = Object.fromEntries(nodes.map((n) => [n.id, n]));
  const implications = map.edges.filter((e) => !e.kind);

  const svg = s('svg', { viewBox: `0 0 ${map.w} ${map.h}`, class: 'bounds-map', role: 'img', 'aria-label': map.title }, ui.stage);
  const defs = s('defs', {}, svg);
  const marker = (id) => `url(#bm-${key}-${id})`;
  for (const [id, cls] of [['head', 'bm-head'], ['hot', 'bm-head hot'], ['todo', 'bm-head todo'], ['alg', 'bm-head alg']]) {
    const m = s('marker', { id: `bm-${key}-${id}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    s('path', { d: 'M0,0 L10,5 L0,10 z', class: cls }, m);
  }

  const caption = h('div', { class: 'bm-caption' });
  ui.state.append(caption);
  const idle = bigo ? 'Hover over a bound, an algorithm or an arrow.' : 'Hover over a bound or an arrow.';
  caption.textContent = idle;

  const link = (names) => names.map((n) => {
    const href = hrefFor(n);
    return href ? `<a href="${esc(href)}"><code>${esc(n)}</code></a>` : `<code>${esc(n)}</code>`;
  }).join(', ');
  const pending = ` <em>Not formalized yet</em>${roadmap ? `; see the <a href="${esc(roadmap)}">roadmap</a>` : ''}.`;
  const sym = (n) => n.alg ? n.label : n.parts.map((p) => p.sym).join(' = ');

  // Edges.
  const edgeEls = [];
  for (const e of map.edges) {
    const a = byId[e.from], b = byId[e.to];
    let [x1, y1] = clip(a, b.x, b.y), [x2, y2] = clip(b, a.x, a.y);
    if (e.off) {
      const len = Math.hypot(x2 - x1, y2 - y1), ox = -(y2 - y1) / len * e.off, oy = (x2 - x1) / len * e.off;
      x1 += ox; x2 += ox; y1 += oy; y2 += oy;
    }
    const kind = e.kind || 'imp';
    const g = s('g', { class: `bm-edge ${kind}${e.todo ? ' todo' : ''}`, tabindex: 0 }, svg);
    s('line', { x1, y1, x2, y2, class: 'bm-hit' }, g);
    const line = s('line', { x1, y1, x2, y2, class: 'bm-line' }, g);
    const rest = kind === 'not' ? '' : marker(e.todo ? 'todo' : kind === 'alg' ? 'alg' : 'head');
    if (rest) line.setAttribute('marker-end', rest);
    const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
    if (e.label) {
      const horizontal = Math.abs(y2 - y1) < 1;
      const [tx, ty, anchor] = e.lab || (kind === 'not' ? [mx, my - 10, 'middle']
        : horizontal ? [mx, my - 8, 'middle'] : [mx + 8, my + 4, 'start']);
      const label = s('text', { x: tx, y: ty, class: 'bm-label', 'text-anchor': anchor }, g);
      label.textContent = e.label;
    }
    if (kind === 'not') {
      const c = s('text', { x: mx, y: my + 5, class: 'bm-cross', 'text-anchor': 'middle' }, g);
      c.textContent = '✗';
    }
    const show = () => {
      clear();
      g.classList.add('hot');
      if (rest) line.setAttribute('marker-end', marker('hot'));
      const rel = kind === 'not' ? '⇏' : '→';
      const ratio = kind === 'alg' && e.label ? ` (${esc(e.label)})` : '';
      const status = e.todo ? pending : ` <span class="bm-thm">${link(e.thms)}</span>`;
      caption.innerHTML = `<strong>${esc(sym(a))} ${rel} ${esc(sym(b))}${ratio}.</strong> ${esc(e.text)}${status}`;
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => {
      const href = e.todo ? roadmap : hrefFor(e.thms[0]);
      if (href) location.href = href;
    });
    edgeEls.push({ e, g, line, rest });
  }

  // Bounds and algorithms.
  const nodeEls = new Map();
  for (const n of nodes) {
    const g = s('g', { class: `bm-node${n.lower ? ' lower' : ''}${n.alg ? ' alg' : ''}`, tabindex: 0 }, svg);
    if (n.alg) {
      s('rect', { x: n.x - n.w / 2, y: n.y - n.h / 2, width: n.w, height: n.h, rx: n.h / 2 }, g);
      const t1 = s('text', { x: n.x, y: n.y + (n.sub ? -2 : 4), class: 'bm-alg', 'text-anchor': 'middle' }, g);
      t1.textContent = n.label;
      if (n.sub) {
        const t2 = s('text', { x: n.x, y: n.y + 11, class: 'bm-name', 'text-anchor': 'middle' }, g);
        t2.textContent = n.sub;
      }
    } else {
      s('rect', { x: n.x - n.w / 2, y: n.y - n.h / 2, width: n.w, height: n.h, rx: 8 }, g);
      const k = n.parts.length;
      n.parts.forEach((p, i) => {
        const cx = n.x - n.w / 2 + (i + 0.5) * (n.w / k);
        const t1 = s('text', { x: cx, y: n.y - 3, class: 'bm-sym', 'text-anchor': 'middle' }, g);
        t1.textContent = p.sym;
        const t2 = s('text', { x: cx, y: n.y + 15, class: 'bm-name', 'text-anchor': 'middle' }, g);
        t2.textContent = p.name;
        if (i > 0) {
          const sx = n.x - n.w / 2 + i * (n.w / k);
          s('line', { x1: sx, y1: n.y - n.h / 2 + 6, x2: sx, y2: n.y + n.h / 2 - 6, class: 'bm-split' }, g);
          const eq = s('text', { x: sx, y: n.y + 5, class: 'bm-eq', 'text-anchor': 'middle' }, g);
          eq.textContent = '=';
        }
      });
    }
    const show = () => {
      clear();
      const out = map.edges.filter((e) => e.from === n.id && e.kind === 'alg');
      const targets = n.alg ? out.map((e) => e.to) : [n.id];
      const proved = reach(n.alg ? out.filter((e) => !e.todo).map((e) => e.to) : targets, false, false);
      const all = reach(targets, false, true);
      const up = n.alg ? new Set() : reach([n.id], true, true);
      const upProved = n.alg ? new Set() : reach([n.id], true, false);
      const metBy = n.alg ? [] : map.edges.filter((e) => e.kind === 'alg' && up.has(e.to));
      const metIds = new Set(metBy.map((e) => e.from));
      for (const [id, el] of nodeEls) {
        const self = id === n.id;
        el.classList.toggle('focus', self);
        el.classList.toggle('down', !self && all.has(id));
        el.classList.toggle('todo', !self && all.has(id) && !proved.has(id));
        el.classList.toggle('up', !self && up.has(id) && !all.has(id));
        el.classList.toggle('dim', !self && !all.has(id) && !up.has(id) && !metIds.has(id));
      }
      for (const { e, g: eg } of edgeEls) {
        const between = (set) => set.has(e.from) && set.has(e.to);
        const on = e.kind === 'alg' ? e.from === n.id || metBy.includes(e)
          : e.kind === 'not' ? e.from === n.id || e.to === n.id
          : between(all) || between(up);
        eg.classList.toggle('dim', !on);
      }
      const names = (set, skip = []) => [...set].filter((id) => id !== n.id && !skip.includes(id)).map((id) => sym(byId[id]));
      const list = (xs) => xs.length ? xs.join(', ') : 'none in this map';
      const proven = names(proved, targets);
      const later = names(all, targets).filter((x) => !proven.includes(x));
      const tail = later.length ? `; and, once formalized, <strong>${esc(later.join(', '))}</strong>` : '';
      function metText() {
        if (!map.algs.length) return '';
        const fmt = (e) => `${byId[e.from].label}${e.label ? ` (within ${e.label})` : ''}`;
        // One entry per algorithm, keeping its best ratio (an unlabelled arrow is constant).
        const best = (es) => [...new Map(es.map((e) => [e.from, e])).keys()]
          .map((id) => es.filter((e) => e.from === id).sort((x, y) => !!x.label - !!y.label)[0]);
        const now = best(metBy.filter((e) => !e.todo && upProved.has(e.to)));
        const later = best(metBy.filter((e) => !now.some((f) => f.from === e.from)));
        const a = now.length ? ` Met by: <strong>${esc(now.map(fmt).join(', '))}</strong>` : ' No algorithm in this map is proved to meet it';
        return `${a}${later.length ? `; once formalized, also by <strong>${esc(later.map(fmt).join(', '))}</strong>` : ''}.`;
      }
      if (n.alg) {
        const meets = out.map((e) => `${sym(byId[e.to])}${e.label ? ` within ${e.label}` : ''}${e.todo ? ' (not formalized yet)' : ''}`);
        caption.innerHTML = `<strong>${esc(n.label)}</strong>${n.sub ? ` (${esc(n.sub)})` : ''} meets <strong>${esc(meets.join('; '))}</strong>. Hence, with the same ratio, it meets: <strong>${esc(list(proven))}</strong>${tail}. <a href="${esc(n.href)}">Open its chapter.</a>`;
      } else {
        const what = n.lower ? 'This is a lower bound: every execution costs at least a constant fraction of it.'
          : `A bound in terms of it implies bounds in terms of: <strong>${esc(list(proven))}</strong>${tail}. It follows from a bound in terms of: <strong>${esc(list(names(up)))}</strong>.${metText()}`;
        const which = n.parts.map((p) => `<strong>${esc(p.sym)}</strong>, ${esc(p.name)} (${link([p.def])})`).join('; ');
        const note = n.note ? `${esc(n.note)} <span class="bm-thm">${link(n.thms)}</span> ` : '';
        caption.innerHTML = `${which}. ${note}${what}`;
      }
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => {
      const href = n.alg ? n.href : hrefFor(n.parts[0].def);
      if (href) location.href = href;
    });
    nodeEls.set(n.id, g);
  }
  svg.addEventListener('mouseleave', () => { clear(); caption.textContent = idle; });

  function clear() {
    for (const el of nodeEls.values()) el.classList.remove('focus', 'down', 'up', 'dim', 'todo');
    for (const { g, line, rest } of edgeEls) {
      g.classList.remove('hot', 'dim');
      if (rest) line.setAttribute('marker-end', rest);
    }
  }

  // Bounds reachable along implication arrows, forward or backward, with or
  // without the arrows that are not formalized yet.
  function reach(starts, backward, withTodo) {
    const seen = new Set(starts);
    const stack = [...starts];
    while (stack.length) {
      const u = stack.pop();
      for (const e of implications) {
        if (e.todo && !withTodo) continue;
        const [p, q] = backward ? [e.to, e.from] : [e.from, e.to];
        if (p === u && !seen.has(q)) { seen.add(q); stack.push(q); }
      }
    }
    return seen;
  }
}
