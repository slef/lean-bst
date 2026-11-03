// The offline construction of Structures/Treap: a GreedyASS point set (below,
// key × time, time growing downwards) and the BST it is realized by (above).
// Before row t the tree is a treap by next-touch time; the keys touched on
// row t are exactly its top region, which is then rearranged into heap order
// for time t+1 while every hanging subtree stays as it is.

import { TreeView } from './render.js';
import { fill } from './geometry.js';
import * as R from './treap-lib.js';
import { button, esc, frame, h, label, number, select } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const el = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (parent) parent.appendChild(e);
  return e;
};

let styled = false;
function style() {
  if (styled) return;
  styled = true;
  document.head.append(h('style', {}, `
.treap-wrap { display: flex; flex-direction: column; align-items: center; width: 100%; }
.treap-wrap .tv { width: 100%; display: flex; justify-content: center; }
.treap-grid { width: 100%; height: auto; overflow: visible; }
.treap-grid .band { fill: var(--target-soft); }
.treap-grid .col { fill: var(--accent-soft); }
.treap-grid .gridline { stroke: var(--rule); stroke-width: 1; }
.treap-grid .tlabel { font-family: var(--mono); font-size: 9px; fill: var(--fg-faint); }
.treap-grid .pt { fill: var(--accent); }
.treap-grid .pt.req { fill: var(--target); }
.treap-grid .pt.future { opacity: .45; }
.treap-prio { font-family: var(--mono); font-size: 9px; fill: var(--fg-faint); text-anchor: middle; pointer-events: none; }
.treap-prio.touched { fill: var(--target); font-weight: 700; }
`));
}

function parse(text, n) {
  const xs = text.split(/[\s,]+/).filter(Boolean).map(Number);
  return xs.every((x) => Number.isInteger(x) && x >= 0 && x < n) ? xs : null;
}

export default function mount(root, cfg) {
  style();
  let n = cfg.n ?? 8;
  let text = (cfg.requests ?? [3, 5, 1, 6, 3, 0, 7, 3, 4]).join(' ');
  let prio = 'next';
  let step = 0; // 2t: before row t (region highlighted); 2t+1: after rearranging row t
  let hover = null;
  let model = null;

  const ui = frame(root, {
    title: cfg.title ?? 'A next-touch treap serving a GreedyASS point set',
    help: 'The points below are the GreedyASS solution for the requests (time grows downwards; orange = request). Each step either highlights the region touched by the current row or rearranges it into heap order for the next time. Small numbers under the nodes are the priorities.',
  });
  const input = h('input', { type: 'text', class: 'vtext', value: text, 'aria-label': 'request sequence', spellcheck: 'false' });
  input.addEventListener('change', () => { text = input.value; rebuild(); });
  const prev = button('◀', () => { if (step > 0) { step--; draw(); } }, { 'aria-label': 'previous step' });
  const next = button('▶', () => { if (model && step < 2 * model.m) { step++; draw(); } }, { 'aria-label': 'next step' });
  ui.controls.append(
    label('requests', input),
    label('n', number(n, { min: 2, max: 16, label: 'number of keys', onChange: (v) => { n = v; rebuild(); } })),
    label('priority', select([['next', 'next touch'], ['last', 'last touch']], prio, (v) => { prio = v; draw(false); })),
    prev, next,
    button('Reset', () => { step = 0; draw(); }),
  );

  const wrap = h('div', { class: 'treap-wrap' });
  ui.stage.append(wrap);
  const tv = new TreeView(wrap, { dx: 40, onHover: (k) => { hover = k; drawGrid(); } });
  const grid = el('svg', { class: 'treap-grid', role: 'img', 'aria-label': 'point set' });
  wrap.append(grid);
  const prios = el('g', {}, tv.svg);

  function rebuild() {
    const xs = parse(text, n);
    if (!xs || xs.length === 0) {
      model = null;
      ui.state.replaceChildren(h('div', { class: 'vnote vno', html: `Type one or more ranks below n = ${n}.` }));
      return;
    }
    const P = fill(xs);
    const { trees, regions } = R.construction(n, P, xs.length);
    model = { xs, P, trees, regions, m: xs.length };
    step = 0;
    draw(false);
  }

  const time = () => Math.floor(step / 2);
  const treeAt = () => model.trees[Math.ceil(step / 2)];
  // The priority the current tree is heap-ordered by.
  const prioTime = () => Math.ceil(step / 2);

  function priorityLabel(x) {
    const t = prioTime();
    if (prio === 'next') { const v = R.nextTouch(model.P, t, x); return v === Infinity ? '∞' : String(v); }
    const v = R.lastTouch(R.pastPoints(model.P, t), x);
    return v === -Infinity ? '⊥' : String(v);
  }

  async function draw(animate = true) {
    if (!model) return;
    const t = time();
    const row = t < model.m ? new Set(model.regions[t].keys) : new Set();
    const classes = new Map();
    for (const x of row) classes.set(x, x === model.xs[t] ? 'target' : 'moved');
    prios.replaceChildren();
    drawGrid();
    drawState(row);
    prev.disabled = step === 0;
    next.disabled = step === 2 * model.m;
    await tv.update(treeAt(), { animate, classes });
    drawPrios(row);
  }

  function drawPrios(row) {
    prios.replaceChildren();
    tv.svg.append(prios);
    for (const [x, p] of tv.pos) {
      const e = el('text', { x: p.x, y: p.y + 24, class: `treap-prio ${row.has(x) ? 'touched' : ''}` }, prios);
      e.textContent = priorityLabel(x);
    }
    // Leave room for the labels below the deepest nodes.
    const vb = tv.svg.getAttribute('viewBox').split(' ').map(Number);
    tv.svg.setAttribute('viewBox', `${vb[0]} ${vb[1]} ${vb[2]} ${vb[3] + 10}`);
  }

  function drawGrid() {
    if (!model) return;
    const g = tv.geometry(treeAt());
    const dy = 18;
    const top = 6;
    const height = top * 2 + model.m * dy;
    grid.setAttribute('viewBox', `0 0 ${g.width} ${height}`);
    grid.style.maxWidth = `${g.width}px`;
    grid.replaceChildren();
    const y = (t) => top + t * dy + dy / 2;
    const t = time();
    if (t < model.m) el('rect', { x: 0, y: y(t) - dy / 2, width: g.width, height: dy, rx: 4, class: 'band' }, grid);
    if (hover !== null) el('rect', { x: g.x(hover) - 9, y: 0, width: 18, height, rx: 4, class: 'col' }, grid);
    for (let s = 0; s < model.m; s++) {
      el('line', { x1: g.x(0) - 12, x2: g.x(n - 1) + 12, y1: y(s), y2: y(s), class: 'gridline' }, grid);
      el('text', { x: 2, y: y(s) + 3, class: 'tlabel' }, grid).textContent = String(s);
    }
    for (const [x, s] of model.P) {
      const req = model.xs[s] === x;
      const c = el('circle', { cx: g.x(x), cy: y(s), r: req ? 5 : 4, class: `pt ${req ? 'req' : ''} ${s > t ? 'future' : ''}` }, grid);
      el('title', {}, c).textContent = `(${x}, ${s})${req ? ' request' : ''}`;
    }
  }

  function drawState(row) {
    const t = time();
    const tree = treeAt();
    const pt = prioTime();
    const heap = R.isHeap((x) => R.nextTouch(model.P, pt, x), tree);
    const hist = R.isHistoryHeap(R.pastPoints(model.P, pt), tree);
    const ok = (b) => (b ? '<span class="vok">holds</span>' : '<span class="vno">fails</span>');
    const rows = [];
    const r = (k, v) => rows.push(h('div', { class: 'vrow' }, h('span', { class: 'vk' }, k), h('span', { class: 'vv', html: v })));
    const done = model.regions.slice(0, Math.floor((step + 1) / 2)).reduce((s, g) => s + g.keys.length, 0);
    if (t < model.m && step % 2 === 0) {
      r(`row ${t}, request ${model.xs[t]}`, `touched keys {${esc([...row].join(', '))}}: the top region of the tree (<code>Region.project</code>)`);
    } else if (t < model.m) {
      r(`row ${t} rearranged`, `region {${esc([...row].join(', '))}} now in heap order for time ${t + 1}; hanging subtrees unchanged`);
    } else {
      r('done', `all ${model.m} rows served`);
    }
    r(`Heap (nextTouch P ${pt})`, ok(heap));
    r('HistoryHeap of the past', ok(hist));
    r('cost so far', `${done} touched nodes; |P| = ${model.P.length}`);
    ui.state.replaceChildren(...rows);
  }

  rebuild();
}
