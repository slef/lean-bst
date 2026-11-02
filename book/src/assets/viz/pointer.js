// The single-cursor pointer machine of Pointer/Machine/Abstract. Every button
// is one constructor of `Pointer.Step`, enabled exactly when its pattern
// matches the current configuration.

import * as T from './tree.js';
import { TreeView } from './render.js';
import { button, frame, mono, row } from './ui.js';

const STEPS = [
  ['downLeft', 'down left', (c) => c.focus && c.focus[0] !== null, (c) => ({ focus: c.focus[0], context: [T.left(c.focus[1]), ...c.context] })],
  ['downRight', 'down right', (c) => c.focus && c.focus[1] !== null, (c) => ({ focus: c.focus[1], context: [T.right(c.focus[0]), ...c.context] })],
  ['upLeft', 'up (from a left child)', (c) => c.context[0]?.side === 'left', (c) => ({ focus: T.node(c.focus, c.context[0].tree), context: c.context.slice(1) })],
  ['upRight', 'up (from a right child)', (c) => c.context[0]?.side === 'right', (c) => ({ focus: T.node(c.context[0].tree, c.focus), context: c.context.slice(1) })],
  ['rotateLeftChild', 'rotate over parent (left child)', (c) => c.context[0]?.side === 'left',
    (c) => ({ focus: T.node(c.focus[0], T.node(c.focus[1], c.context[0].tree)), context: c.context.slice(1) })],
  ['rotateRightChild', 'rotate over parent (right child)', (c) => c.context[0]?.side === 'right',
    (c) => ({ focus: T.node(T.node(c.context[0].tree, c.focus[0]), c.focus[1]), context: c.context.slice(1) })],
];

export default function mount(root, cfg) {
  const start = cfg.tree ? T.fromLean(cfg.tree) : T.randomTree(cfg.n ?? 9, cfg.seed ?? 3);
  let requests = cfg.requests ?? [4, 1, 6];
  let req = 0;
  let config;
  let s; // tree at the start of the current request
  let before; let after; let visited; let total; let log;

  const ui = frame(root, {
    title: cfg.title ?? 'The pointer machine',
    help: 'Each button is a constructor of Pointer.Step and costs one. A search starts at the root and must put the cursor on the requested key at some point; it may keep working afterwards.',
  });
  const view = new TreeView(ui.stage, {});
  const buttons = STEPS.map(([name, text, ok, apply]) => {
    const b = button(`.${name}`, () => {
      if (!ok(config)) return;
      config = apply(config);
      if (visited === null) before++; else after++;
      log.push(name);
      if (visited === null && T.keyOf(config) === requests[req]) visited = before;
      draw();
    }, { title: text, class: 'vbtn mono' });
    return b;
  });
  const next = button('Finish request', () => {
    if (visited === null) return;
    total += 1 + before + after;
    req = (req + 1) % requests.length;
    begin(T.plug(config.context, config.focus));
  }, { class: 'vbtn primary' });
  const reset = button('Reset', () => { req = 0; total = 0; begin(start); });
  ui.controls.append(...buttons, next, reset);

  function begin(tree) {
    s = tree;
    config = { focus: tree, context: [] };
    before = 0; after = 0; log = [];
    visited = T.keyOf(config) === requests[req] ? 0 : null;
    draw();
  }

  function draw() {
    const whole = T.plug(config.context, config.focus);
    const cursor = T.keyOf(config);
    const classes = new Map();
    classes.set(requests[req], 'target');
    if (cursor !== null) classes.set(cursor, `${classes.get(cursor) ?? ''} cursor`);
    view.update(whole, { classes });
    STEPS.forEach(([, , ok], i) => { buttons[i].disabled = !ok(config); });
    next.disabled = visited === null;

    const frames = config.context.map((f) => `.${f.side} ⟨${T.size(f.tree)} key${T.size(f.tree) === 1 ? '' : 's'}⟩`);
    ui.state.replaceChildren(
      row('request', `x = ${requests[req]} <span class="vnote">(sequence ${requests.join(', ')})</span>`),
      row('Config', `${mono(`⟨focus, [${frames.join(', ')}]⟩`)} <span class="vnote">focus has ${T.size(config.focus)} keys</span>`),
      row('key?', `${mono(`offset context + l.size = ${T.offset(config.context)} + ${config.focus ? T.size(config.focus[0]) : 0} = ${cursor}`)}`),
      row('trace', log.length ? mono(log.map((n) => '.' + n).join(', ')) : '<span class="vnote">empty</span>'),
      row('Serves s t x cost', visited === null
        ? `<span class="vno">not yet visited ${requests[req]}</span> (${before} steps so far)`
        : `<span class="vok">visited</span> after ${before} steps; ${after} more since; cost so far ${mono(`1 + ${before} + ${after} = ${1 + before + after}`)}`),
      row('Execution cost', `${total} for the requests finished so far`),
    );
  }
  total = 0;
  begin(start);
}
