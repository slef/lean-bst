// The geometric view: keys on the horizontal axis, time going upward.
//
// mode "greedy": GreedyASS adds one row per request (geometry.js greedySweep);
//   each projected point is joined to the old point it comes from.
// mode "edit": the reader toggles points; the panel checks ASS and draws an
//   empty rectangle when there is one.
// In both modes, clicking two points shows their rectangle.
//
// Options: n, requests, mode, title, start ("requests" | "greedy", edit mode),
//          shown (number of rows initially revealed, greedy mode).

import * as G from './geometry.js';
import { button, frame, h, label, number, select as dropdown } from './ui.js';

const NS = 'http://www.w3.org/2000/svg';
function s(tag, attrs = {}, ...children) {
  const e = document.createElementNS(NS, tag);
  for (const [k, v] of Object.entries(attrs)) if (v !== undefined && v !== null && v !== false) e.setAttribute(k, v);
  for (const c of children.flat()) if (c) e.append(c);
  return e;
}

const STYLE = `
.geo-svg { max-width: 100%; height: auto; overflow: visible; font-family: var(--mono); }
.geo-grid line { stroke: var(--rule); stroke-width: 1; }
.geo-tick { font-size: 10.5px; fill: var(--fg-faint); }
.geo-axis { font-size: 10.5px; fill: var(--fg-faint); font-family: var(--sans); }
.geo-cell { fill: transparent; }
.geo-cell.clickable { cursor: pointer; }
.geo-cell.clickable:hover { fill: var(--accent-soft); }
.geo-pt { fill: var(--accent); stroke: var(--bg); stroke-width: 1.5; cursor: pointer; }
.geo-pt.req { fill: var(--target); }
.geo-pt.ghost { fill: none; stroke: var(--target); stroke-width: 1.5; stroke-dasharray: 2 2; cursor: default; }
.geo-pt.new { stroke: var(--fg); stroke-width: 1.5; }
.geo-pt.sel { stroke: var(--fg); stroke-width: 2.5; }
.geo-pt.inside { stroke: var(--good); stroke-width: 3; }
.geo-proj { stroke: var(--accent); stroke-width: 1.2; stroke-dasharray: 3 3; }
.geo-vis { fill: var(--accent-soft); fill-opacity: .55; stroke: var(--accent); stroke-width: 1; stroke-dasharray: 3 3; }
.geo-rect { fill: var(--good-soft); fill-opacity: .7; stroke: var(--good); stroke-width: 1.5; }
.geo-rect.empty { fill: var(--warn-soft); stroke: var(--warn); stroke-width: 2; }
.geo-rownow { fill: var(--accent-soft); fill-opacity: .45; }
`;
let styled = false;

export default function mount(root, cfg) {
  if (!styled) { document.head.append(h('style', {}, STYLE)); styled = true; }
  const mode = cfg.mode ?? 'greedy';
  let n = cfg.n ?? 6;
  let requests = (cfg.requests ?? [2, 4, 1, 3, 5, 0, 2]).slice();
  let shown = mode === 'greedy' ? (cfg.shown ?? 0) : requests.length;
  let selected = [];
  let timer = null;
  let points = [];
  let clickMode = 'edit';

  const ui = frame(root, {
    title: cfg.title ?? (mode === 'greedy' ? 'GreedyASS, row by row' : 'Is it arborally satisfied?'),
    help: mode === 'greedy'
      ? 'Keys run left to right and time runs upward; orange points are requests. Each step adds the next row: the request, plus the projection of every old point whose rectangle with the request is empty (shaded). Click two points to see their rectangle.'
      : 'Keys run left to right and time runs upward; orange points are requests and cannot be removed. Click a cell to add or remove a point. To inspect a rectangle, switch the click mode and click two points.',
  });

  const input = h('input', { type: 'text', class: 'vtext', value: requests.join(' '), 'aria-label': 'request sequence', spellcheck: 'false' });
  input.addEventListener('change', () => {
    const xs = input.value.split(/[\s,]+/).filter(Boolean).map(Number);
    if (xs.length === 0 || xs.length > 16 || xs.some((x) => !Number.isInteger(x) || x < 0)) { input.value = requests.join(' '); return; }
    requests = xs;
    n = Math.max(n, Math.max(...xs) + 1);
    nInput.value = n;
    reset();
  });
  const nInput = number(n, {
    min: 1, max: 12, label: 'number of keys',
    onChange: (v) => { n = Math.max(v, Math.max(...requests) + 1); nInput.value = n; reset(); },
  });
  ui.controls.append(label('requests', input), label('n', nInput));

  let playBtn;
  if (mode === 'greedy') {
    const back = button('Back', () => { stop(); if (shown > 0) { shown--; selected = []; recompute(); } });
    const step = button('Step', () => { stop(); if (shown < requests.length) { shown++; selected = []; recompute(); } });
    playBtn = button('Play', () => {
      if (timer) { stop(); return; }
      if (shown >= requests.length) shown = 0;
      playBtn.textContent = 'Pause';
      timer = setInterval(() => {
        if (shown >= requests.length) { stop(); return; }
        shown++; selected = []; recompute();
      }, 700);
    });
    const all = button('All', () => { stop(); shown = requests.length; selected = []; recompute(); });
    ui.controls.append(back, step, playBtn, all);
  } else {
    ui.controls.append(
      dropdown([['edit', 'click edits points'], ['pick', 'click picks a rectangle']], clickMode,
        (v) => { clickMode = v; selected = []; draw(); }, { 'aria-label': 'click mode' }),
      button('Requests only', () => { points = G.requestsAt(0, requests); selected = []; draw(); }),
      button('GreedyASS', () => { points = G.fill(requests); selected = []; draw(); }),
    );
  }

  function stop() {
    if (timer) clearInterval(timer);
    timer = null;
    if (playBtn) playBtn.textContent = 'Play';
  }

  function reset() {
    stop();
    selected = [];
    if (mode === 'greedy') shown = 0;
    else points = cfg.start === 'greedy' ? G.fill(requests) : G.requestsAt(0, requests);
    recompute();
  }

  function recompute() {
    if (mode === 'greedy') points = G.fill(requests.slice(0, shown));
    draw();
  }

  const isRequest = (p) => p[1] < requests.length && requests[p[1]] === p[0];

  function draw() {
    const m = requests.length;
    const cell = Math.max(24, Math.min(40, Math.floor(480 / Math.max(n, m))));
    const ml = 46; const mt = 10; const mb = 34; const mr = 10;
    const W = ml + n * cell + mr; const H = mt + m * cell + mb;
    const X = (k) => ml + k * cell + cell / 2;
    const Y = (t) => mt + (m - 1 - t) * cell + cell / 2;
    const svg = s('svg', { class: 'geo-svg', viewBox: `0 0 ${W} ${H}`, width: Math.round(W * 1.3), height: Math.round(H * 1.3), role: 'img', 'aria-label': 'point set in the key–time plane' });

    // Grid and axes.
    const grid = s('g', { class: 'geo-grid' });
    for (let k = 0; k < n; k++) grid.append(s('line', { x1: X(k), x2: X(k), y1: mt, y2: mt + m * cell }));
    for (let t = 0; t < m; t++) grid.append(s('line', { x1: ml, x2: ml + n * cell, y1: Y(t), y2: Y(t) }));
    svg.append(grid);
    for (let k = 0; k < n; k++) svg.append(s('text', { class: 'geo-tick', x: X(k), y: mt + m * cell + 14, 'text-anchor': 'middle' }, String(k)));
    for (let t = 0; t < m; t++) svg.append(s('text', { class: 'geo-tick', x: ml - 8, y: Y(t) + 3.5, 'text-anchor': 'end' }, String(t)));
    svg.append(s('text', { class: 'geo-axis', x: ml + n * cell / 2, y: H - 4, 'text-anchor': 'middle' }, 'key'));
    svg.append(s('text', { class: 'geo-axis', x: 10, y: mt + m * cell / 2, 'text-anchor': 'middle', transform: `rotate(-90 10 ${mt + m * cell / 2})` }, 'time'));

    // The row just added, with its empty rectangles and projections.
    if (mode === 'greedy' && shown > 0) {
      const t = shown - 1;
      const old = G.fill(requests.slice(0, t));
      svg.append(s('rect', { class: 'geo-rownow', x: ml, y: Y(t) - cell / 2, width: n * cell, height: cell }));
      for (const q of old) {
        if (!G.visible(old, t, requests[t], q)) continue;
        const x0 = Math.min(q[0], requests[t]); const x1 = Math.max(q[0], requests[t]);
        svg.append(s('rect', { class: 'geo-vis', x: X(x0), y: Y(t), width: X(x1) - X(x0), height: Y(q[1]) - Y(t) }));
        svg.append(s('line', { class: 'geo-proj', x1: X(q[0]), y1: Y(q[1]), x2: X(q[0]), y2: Y(t) }));
      }
    }

    // Selected rectangle.
    let rectInfo = null;
    if (selected.length === 2) {
      const [a, b] = selected;
      const inside = points.filter((p) => !G.samePoint(p, a) && !G.samePoint(p, b) && G.rectangle(a, b, p));
      const degenerate = a[0] === b[0] || a[1] === b[1];
      rectInfo = { a, b, inside, degenerate };
      const x0 = Math.min(a[0], b[0]); const x1 = Math.max(a[0], b[0]);
      const t0 = Math.min(a[1], b[1]); const t1 = Math.max(a[1], b[1]);
      const pad = degenerate ? 4 : 0;
      svg.append(s('rect', {
        class: `geo-rect${!degenerate && inside.length === 0 ? ' empty' : ''}`,
        x: X(x0) - pad, y: Y(t1) - pad, width: X(x1) - X(x0) + 2 * pad, height: Y(t0) - Y(t1) + 2 * pad,
      }));
    }

    // Failing rectangle in edit mode.
    const check = G.checkASS(points);
    if (mode === 'edit' && !check.ok && selected.length < 2) {
      const [a, b] = check.witness;
      svg.append(s('rect', {
        class: 'geo-rect empty',
        x: X(Math.min(a[0], b[0])), y: Y(Math.max(a[1], b[1])),
        width: Math.abs(X(a[0]) - X(b[0])), height: Math.abs(Y(a[1]) - Y(b[1])),
      }));
    }

    // Clickable cells (edit mode) and ghost requests (greedy mode, future rows).
    if (mode === 'edit') {
      for (let k = 0; k < n; k++) {
        for (let t = 0; t < m; t++) {
          const c = s('rect', { class: 'geo-cell clickable', x: X(k) - cell / 2, y: Y(t) - cell / 2, width: cell, height: cell });
          c.addEventListener('click', () => toggle([k, t]));
          svg.append(c);
        }
      }
    } else {
      for (let t = shown; t < m; t++) svg.append(s('circle', { class: 'geo-pt ghost', cx: X(requests[t]), cy: Y(t), r: cell * 0.2 }));
    }

    // Points.
    const r = cell * 0.22;
    for (const p of points) {
      const cls = ['geo-pt'];
      if (isRequest(p)) cls.push('req');
      if (mode === 'greedy' && p[1] === shown - 1) cls.push('new');
      if (selected.some((q) => G.samePoint(p, q))) cls.push('sel');
      if (rectInfo?.inside.some((q) => G.samePoint(p, q))) cls.push('inside');
      const c = s('circle', { class: cls.join(' '), cx: X(p[0]), cy: Y(p[1]), r, tabindex: 0 },
        s('title', {}, `(${p[0]}, ${p[1]})`));
      c.addEventListener('click', (e) => {
        e.stopPropagation();
        if (mode === 'edit' && clickMode === 'edit') toggle(p); else select(p);
      });
      svg.append(c);
    }

    ui.stage.replaceChildren(svg);
    panel(check, rectInfo);
  }

  function select(p) {
    const i = selected.findIndex((q) => G.samePoint(p, q));
    if (i >= 0) selected.splice(i, 1);
    else { if (selected.length === 2) selected = []; selected.push(p); }
    draw();
  }

  function toggle(p) {
    if (isRequest(p)) return;
    if (G.has(points, p)) points = points.filter((q) => !G.samePoint(p, q));
    else points = [...points, p];
    selected = [];
    draw();
  }

  const fmtP = (p) => `(${p[0]}, ${p[1]})`;
  const vrow = (k, v) => h('div', { class: 'vrow' }, h('span', { class: 'vk' }, k), h('span', { class: 'vv', html: v }));

  function panel(check, rectInfo) {
    const rows = [];
    if (mode === 'greedy') {
      if (shown === 0) rows.push(vrow('time', '<span class="vnote">no rows yet: press Step</span>'));
      else {
        const t = shown - 1;
        const keys = G.rows(requests.slice(0, shown))[t];
        rows.push(vrow('time, request', `${t}, ${requests[t]}`));
        rows.push(vrow('greedySweep row', `{${keys.join(', ')}} <span class="vnote">(${keys.length} point${keys.length === 1 ? '' : 's'})</span>`));
      }
      rows.push(vrow('rowCost so far', `${points.length} <span class="vnote">for ${shown} request${shown === 1 ? '' : 's'}</span>`));
    } else {
      const reqs = points.filter(isRequest).length;
      rows.push(vrow('points', `${points.length} <span class="vnote">(${reqs} requests + ${points.length - reqs} added)</span>`));
    }
    rows.push(vrow('ASS P', check.ok
      ? '<span class="vok">yes</span>: every rectangle spanned by two points contains a third'
      : `<span class="vno">no</span>: the rectangle of ${fmtP(check.witness[0])} and ${fmtP(check.witness[1])} contains no other point`));
    if (rectInfo) {
      const { a, b, inside, degenerate } = rectInfo;
      let text;
      if (degenerate) text = 'degenerate (same key or same time): no condition';
      else if (inside.length) text = `<span class="vok">satisfied</span> by ${inside.map(fmtP).join(', ')}`;
      else text = '<span class="vno">empty</span>';
      rows.push(vrow(`Rectangle ${fmtP(a)} ${fmtP(b)}`, text));
    } else if (selected.length === 1) {
      rows.push(vrow('selected', `${fmtP(selected[0])} <span class="vnote">click a second point</span>`));
    }
    ui.state.replaceChildren(...rows);
  }

  reset();
  if (mode === 'greedy' && cfg.shown) { shown = Math.min(cfg.shown, requests.length); recompute(); }
}
