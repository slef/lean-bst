// Splay updates on a forest: access, insert, delete, split and join, each
// charged one unit plus its rotations, as in `Updates.Step`. The running total
// is compared with the operation-sensitive bound Σ (5 log₂(nⱼ + 1) + 3).

import * as T from './tree.js';
import { TreeView } from './render.js';
import { button, fmt, frame, h, label, mono, select } from './ui.js';

export default function mount(root, cfg) {
  let forest = [cfg.tree ? T.fromLean(cfg.tree) : T.randomTree(cfg.n ?? 7, cfg.seed ?? 9)];
  let mode = 'access';
  let log = [];
  const ui = frame(root, {
    title: cfg.title ?? 'Updates on a forest of shapes',
    help: 'Choose an operation, then click: a node for access or delete, a square (a gap between ranks) for insert or split. Join merges the first two trees, left keys before right keys.',
  });
  const forestBox = h('div', { class: 'forest' });
  ui.stage.append(forestBox);
  const modeSel = select([['access', 'access x'], ['insert', 'insert in gap k'], ['delete', 'delete x'], ['split', 'split at gap k']], mode, (v) => { mode = v; draw(); });
  const joinBtn = button('Join first two', () => {
    if (forest.length < 2) return;
    const [l, r, ...rest] = forest;
    const [u, c] = T.join(l, r);
    record('join', T.size(l) + T.size(r), c);
    forest = [u, ...rest];
    draw();
  });
  ui.controls.append(label('operation', modeSel), joinBtn,
    button('Reset', () => { forest = [T.randomTree(cfg.n ?? 7, cfg.seed ?? 9)]; log = []; draw(); }),
    button('Empty', () => { forest = [null]; log = []; draw(); }));

  function record(op, n, rotations) {
    log.push({ op, n, cost: rotations + 1, bound: 5 * T.logb2(n + 1) + 3 });
  }

  function draw() {
    forestBox.replaceChildren();
    forest.forEach((t, i) => {
      const cell = h('div', { class: 'forest-tree' }, h('div', { class: 'forest-label' }, `tree ${i + 1} · ${T.size(t)} keys`));
      forestBox.append(cell);
      const view = new TreeView(cell, {
        showGaps: mode === 'insert' || mode === 'split',
        dx: 30, dy: 38, r: 12,
        onNode: (mode === 'access' || mode === 'delete') ? (k) => {
          const n = T.size(t);
          if (mode === 'access') { const [u, c] = T.run(t, k); forest[i] = u; record(`access ${k}`, n, c); }
          else { const [u, c] = T.remove(t, k); forest[i] = u; record(`delete ${k}`, n, c); }
          draw();
        } : null,
        onGap: (mode === 'insert' || mode === 'split') ? (k) => {
          const n = T.size(t);
          if (mode === 'insert') { const [u, c] = T.insert(t, k); forest[i] = u; record(`insert at gap ${k}`, n, c); }
          else { const s = T.split(t, k); forest.splice(i, 1, s.left, s.right); record(`split at gap ${k}`, n, s.cost); }
          draw();
        } : null,
      });
      view.update(t, { animate: false });
      if (t === null && !(mode === 'insert' || mode === 'split')) cell.append(h('div', { class: 'vnote' }, 'empty'));
    });
    joinBtn.disabled = forest.length < 2;
    const total = log.reduce((s, e) => s + e.cost, 0);
    const bound = log.reduce((s, e) => s + e.bound, 0);
    ui.state.replaceChildren(
      h('div', { class: 'vrow' }, h('span', { class: 'vk' }, 'operations'),
        h('span', { class: 'vv', html: log.length ? `<ol class="vsteps">${log.slice(-8).map((e) => `<li>${e.op}: cost ${e.cost} (n = ${e.n}; bound ${fmt(e.bound)})</li>`).join('')}</ol>` : '<span class="vnote">none yet</span>' })),
      h('div', { class: 'vrow' }, h('span', { class: 'vk' }, 'total cost c'), h('span', { class: 'vv', html: `${total} ${log.length ? `≤ Σ (5 log₂(nⱼ+1) + 3) = ${fmt(bound)}` : ''}` })),
      h('div', { class: 'vnote', html: `The bound is ${mono('balance_initially_empty')}; it is proved for executions that start from an empty forest (use “Empty”, then insert). From a nonempty start, ${mono('balance')} adds a startup term.` }),
    );
  }
  draw();
}
