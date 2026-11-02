// Shapes and their implicit keys. Click an empty subtree to grow the shape
// there, click a leaf to remove it; hover a node to see how `Tree.labelFrom`
// computes its key.

import * as T from './tree.js';
import { TreeView } from './render.js';
import { button, frame, mono, row } from './ui.js';

function addAt(t, gap, lo = 0) {
  // Replace the empty subtree that sits in inorder gap `gap` by a leaf.
  if (t === null) return gap === lo ? T.node(null, null) : null;
  const k = lo + T.size(t[0]);
  if (gap <= k) return T.node(addAt(t[0], gap, lo), t[1]);
  return T.node(t[0], addAt(t[1], gap, k + 1));
}
function removeLeaf(t, x, lo = 0) {
  if (t === null) return null;
  const k = lo + T.size(t[0]);
  if (x === k) return t[0] === null && t[1] === null ? null : t;
  if (x < k) return T.node(removeLeaf(t[0], x, lo), t[1]);
  return T.node(t[0], removeLeaf(t[1], x, k + 1));
}

export default function mount(root, cfg) {
  let tree = cfg.tree ? T.fromLean(cfg.tree) : T.randomTree(cfg.n ?? 6, cfg.seed ?? 2);
  let hover = null;
  const ui = frame(root, {
    title: cfg.title ?? 'A shape and its implicit keys',
    help: 'Click a small square (an empty subtree) to put a node there; click a leaf to remove it. Hover a node to see its key computed as in Tree.labelFrom.',
  });
  const view = new TreeView(ui.stage, {
    showGaps: true,
    onGap: (gap) => { tree = addAt(tree, gap); draw(false); },
    onNode: (k) => { const u = removeLeaf(tree, k); if (!T.equal(u, tree)) { tree = u; draw(false); } },
    onHover: (k) => { hover = k; info(); },
  });
  ui.controls.append(
    button('Random', () => { tree = T.randomTree(1 + Math.floor(Math.random() * 9), Math.floor(Math.random() * 1e6)); draw(false); }),
    button('Balanced', () => { tree = T.balanced(7); draw(false); }),
    button('Path', () => { tree = T.leftPath(5); draw(false); }),
    button('Empty', () => { tree = null; draw(false); }),
  );

  function info() {
    ui.state.replaceChildren();
    ui.state.append(row('Lean term', mono(T.toLean(tree)), 'lean-term'));
    ui.state.append(row('Tree.size', String(T.size(tree))));
    if (hover !== null) {
      const v = T.layout(tree).find((u) => u.key === hover);
      if (v) {
        ui.state.append(row(`key of node ${hover}`,
          `its subtree is labelled from <code>lo = ${v.subtreeLo}</code> and has ${v.subtreeSize} key${v.subtreeSize === 1 ? '' : 's'}; `
          + `its left subtree has <code>l.size = ${v.leftSize}</code>, so its key is <code>lo + l.size = ${v.subtreeLo} + ${v.leftSize} = ${hover}</code>`));
      }
    } else {
      ui.state.append(row('', '<span class="vnote">Hover a node.</span>'));
    }
  }
  function draw(animate = true) {
    view.update(tree, { animate, classes: new Map(hover !== null ? [[hover, 'target']] : []) });
    info();
  }
  draw(false);
}
