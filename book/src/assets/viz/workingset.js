// Per-request charges of the sequence measures in WorkingSet/Abstract and
// Bounds/Abstract, for a sequence the reader types.

import * as T from './tree.js';
import { esc, fmt, frame, h, label, number } from './ui.js';

export default function mount(root, cfg) {
  let n = cfg.n ?? 8;
  let f = cfg.finger ?? 0;
  let text = (cfg.requests ?? [3, 5, 3, 1, 5, 5, 0, 3]).join(' ');
  const ui = frame(root, {
    title: cfg.title ?? 'Sequence measures, request by request',
    help: 'Type ranks separated by spaces. The columns are the per-request terms of workingSetSum, staticCost and fingerCost.',
  });
  const input = h('input', { type: 'text', class: 'vtext', value: text, 'aria-label': 'request sequence', spellcheck: 'false' });
  input.addEventListener('input', () => { text = input.value; draw(); });
  ui.controls.append(
    label('requests', input),
    label('n', number(n, { min: 1, max: 64, label: 'number of keys', onChange: (v) => { n = v; draw(); } })),
    label('finger f', number(f, { min: 0, max: 63, label: 'finger', onChange: (v) => { f = v; draw(); } })),
  );
  function draw() {
    const xs = text.split(/[\s,]+/).filter(Boolean).map(Number);
    const bad = xs.filter((x) => !Number.isInteger(x) || x < 0 || x >= n);
    ui.stage.replaceChildren();
    if (bad.length) {
      ui.stage.append(h('div', { class: 'vnote vno', html: `Every request must be a rank below n = ${n} (the hypothesis <code>∀ x ∈ xs, x &lt; t.size</code>).` }));
      ui.state.replaceChildren();
      return;
    }
    const rows = [];
    let ws = 0; let st = xs.length; let fc = 0;
    const counts = new Map();
    for (const x of xs) counts.set(x, (counts.get(x) ?? 0) + 1);
    xs.forEach((x, j) => {
      const past = xs.slice(0, j);
      const w = T.workingSetNumber(n, past, x);
      const wsTerm = 1 + T.natLog2(w);
      ws += wsTerm;
      const freq = T.logb2(xs.length / counts.get(x));
      const fin = 1 + T.logb2(Math.abs(x - f) + 1);
      fc += fin;
      const since = past.includes(x) ? past.slice(past.lastIndexOf(x) + 1) : null;
      rows.push(h('tr', {},
        h('td', {}, String(j + 1)),
        h('td', { class: 'num' }, String(x)),
        h('td', { html: since === null ? '<span class="vnote">first access</span>' : `{${esc([...new Set(since)].join(', '))}}` }),
        h('td', { class: 'num' }, String(w)),
        h('td', { class: 'num' }, String(wsTerm)),
        h('td', { class: 'num' }, fmt(1 + freq)),
        h('td', { class: 'num' }, fmt(fin)),
      ));
    });
    void st;
    ui.stage.append(h('div', { class: 'table-wrap' }, h('table', { class: 'vtable' },
      h('thead', {}, h('tr', {}, ...['j', 'x', 'distinct keys since last x', 'workingSetNumber', '1 + ⌊log₂⌋', '1 + log₂(m/qₓ)', '1 + log₂(|x−f|+1)'].map((c) => h('th', {}, c)))),
      h('tbody', {}, ...rows))));
    ui.state.replaceChildren(
      h('div', { class: 'vrow' }, h('span', { class: 'vk' }, 'workingSetSum n [] xs'), h('span', { class: 'vv' }, String(T.workingSetSum(n, [], xs)))),
      h('div', { class: 'vrow' }, h('span', { class: 'vk' }, 'Bounds.staticCost n xs'), h('span', { class: 'vv' }, fmt(T.staticCost(n, xs)))),
      h('div', { class: 'vrow' }, h('span', { class: 'vk' }, `Bounds.fingerCost ${f} xs`), h('span', { class: 'vv' }, fmt(fc))),
    );
  }
  draw();
}
