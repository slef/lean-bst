// Rotation playground: click a node to rotate it over its parent. Shows the
// `Rotate` derivation for each step, the running `Rotations s t k` count, and,
// with a target rank, whether `Access s t x k` holds.

import * as T from './tree.js';
import { TreeView } from './render.js';
import { button, esc, frame, label, mono, number, row, select } from './ui.js';

export default function mount(root, cfg) {
  const keys = cfg.keys ?? null;
  const target = cfg.target ?? null;
  let n = cfg.n ?? (keys ? keys.length : 7);
  let shape = cfg.shape ?? 'random';
  let seed = cfg.seed ?? 4;
  const initialFromCfg = cfg.tree ? T.fromLean(cfg.tree) : null;
  let start = initialFromCfg ?? T.makeTree(shape, n, seed);
  let tree = start;
  let history = [];

  const ui = frame(root, {
    title: cfg.title ?? (target !== null ? `Bring key ${keys ? keys[target] : target} to the root` : 'Rotations'),
    help: 'Click a node to rotate it above its parent. Horizontal position is the inorder rank, so nodes only move up and down.',
  });

  const labelOf = (k) => (keys ? keys[k] : String(k));
  const view = new TreeView(ui.stage, {
    label: labelOf,
    onNode: (k) => {
      const r = T.rotateUp(tree, k);
      if (!r) return;
      history.push({ term: r.term, before: tree, key: k });
      tree = r.tree;
      draw();
    },
  });

  const undo = button('Undo', () => { const h = history.pop(); if (h) { tree = h.before; draw(); } });
  const reset = button('Reset', () => { tree = start; history = []; draw(); });
  ui.controls.append(undo, reset);
  if (!initialFromCfg && !keys) {
    ui.controls.prepend(
      label('shape', select([['random', 'random'], ['balanced', 'balanced'], ['left-path', 'left path'], ['right-path', 'right path'], ['zigzag', 'zigzag']], shape, (v) => { shape = v; regenerate(); })),
      label('n', number(n, { min: 1, max: 24, label: 'number of keys', onChange: (v) => { n = v; regenerate(); } })),
      button('New', () => { seed += 1; regenerate(); }),
    );
  }
  function regenerate() { start = T.makeTree(shape, n, seed); tree = start; history = []; draw(); }

  function draw() {
    const classes = new Map();
    if (target !== null) classes.set(target, 'target');
    const rootKey = T.rootKey(tree);
    if (rootKey !== null && !classes.has(rootKey)) classes.set(rootKey, 'root');
    if (history.length) {
      const last = history[history.length - 1].key;
      classes.set(last, `${classes.get(last) ?? ''} moved`);
    }
    view.update(tree, { classes });
    undo.disabled = history.length === 0;
    reset.disabled = history.length === 0;

    const k = history.length;
    ui.state.replaceChildren();
    ui.state.append(row('current tree', mono(T.toLean(tree)), 'lean-term'));
    if (keys) {
      const inorder = T.layout(tree).map((v) => keys[v.key]);
      ui.state.append(row('inorder', mono(`[${inorder.join(', ')}]`) + ' <span class="vnote">unchanged by every rotation</span>'));
    }
    if (k > 0) {
      const steps = history.map((h, i) => `<li>${mono(h.term)}</li>`).join('');
      ui.state.append(row('last step', `${mono(`Rotate s t`)} by ${mono(history[k - 1].term)}`));
      ui.state.append(row(`Rotations s t ${k}`, `<ol class="vsteps">${steps}</ol>`));
    } else {
      ui.state.append(row('Rotations s s 0', `${mono('Rotations.refl')} <span class="vnote">no rotations yet</span>`));
    }
    if (target !== null) {
      const ok = rootKey === target;
      const l = tree ? T.size(tree[0]) : 0;
      const what = keys ? `the root holds ${keys[rootKey]}, rank ${l}` : `the root's left subtree has size ${l}`;
      ui.state.append(row(`Access s t ${labelOf(target)} ${k}`, ok
        ? `<span class="vok">holds</span>: ${what}${keys ? '' : ` = ${target}`}`
        : `<span class="vno">not yet</span>: ${what}${keys ? `, not ${labelOf(target)}` : `, not ${target}`}`));
    }
  }
  draw();
  void esc;
}
