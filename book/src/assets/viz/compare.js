// Move-to-root against splaying: cumulative rotations of the two JavaScript
// ports (T.moveToRoot, T.run) on the same initial tree and request sequence.

import * as T from './tree.js';
import { button, fmt, frame, h, label, number, select } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const s = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  parent?.appendChild(e);
  return e;
};

function sequence(kind, n, m, seed) {
  const r = T.rng(seed);
  const hot = Array.from({ length: Math.max(1, Math.round(Math.log2(n))) }, () => Math.floor(r() * n));
  const out = [];
  for (let j = 0; j < m; j++) {
    if (kind === 'sequential') out.push(j % n);
    else if (kind === 'workingset') out.push(r() < 0.9 ? hot[Math.floor(r() * hot.length)] : Math.floor(r() * n));
    else out.push(Math.floor(r() * n));
  }
  return out;
}

export default function mount(root, cfg) {
  let kind = cfg.sequence ?? 'sequential';
  let shape = cfg.shape ?? 'left-path';
  let n = cfg.n ?? 63;
  let m = cfg.m ?? 4 * n;
  let seed = 3;
  const ui = frame(root, {
    title: cfg.title ?? 'Move-to-root against splaying',
    help: 'Both algorithms start from the same tree and serve the same requests. The curves count rotations only, as Algorithm.cost does.',
  });
  ui.controls.append(
    label('requests', select([['sequential', 'sequential scans'], ['uniform', 'uniform random'], ['workingset', 'small working set']], kind, (v) => { kind = v; draw(); })),
    label('start', select([['left-path', 'left path'], ['balanced', 'balanced'], ['random', 'random']], shape, (v) => { shape = v; draw(); })),
    label('n', number(n, { min: 2, max: 255, label: 'number of keys', onChange: (v) => { n = v; draw(); } })),
    label('m', number(m, { min: 1, max: 4000, label: 'number of requests', onChange: (v) => { m = v; draw(); } })),
    button('Resample', () => { seed++; draw(); }),
  );
  const chartBox = h('div', { class: 'chart' });
  ui.stage.append(chartBox);
  ui.stage.classList.add('chart-stage');

  function draw() {
    const xs = sequence(kind, n, m, seed);
    const series = [T.run, T.moveToRoot].map((step) => {
      let t = T.makeTree(shape, n, seed);
      let R = 0;
      const out = [0];
      for (const x of xs) { const [u, c] = step(t, x); t = u; R += c; out.push(R); }
      return out;
    });
    plot(series[0], series[1]);
    const [a, b] = [series[0][m], series[1][m]];
    ui.state.replaceChildren(
      h('div', { class: 'chart-legend' },
        h('span', {}, h('span', { class: 'key s1' }), 'splaying (Splay.run)'),
        h('span', {}, h('span', { class: 'key s2' }), 'move-to-root (moveToRoot)')),
      h('div', { class: 'vnote', html: `After ${m} requests: splaying ${fmt(a, 0)} rotations (${fmt(a / m, 1)} per request), move-to-root ${fmt(b, 0)} (${fmt(b / m, 1)} per request).` }),
    );
  }

  function plot(a, b) {
    chartBox.querySelector('svg')?.remove();
    const W = 680; const H = 280;
    const M = { l: 56, r: 24, t: 16, b: 34 };
    const svg = s('svg', { viewBox: `0 0 ${W} ${H}`, class: 'chart-svg', role: 'img', 'aria-label': 'Cumulative rotations of splaying and move-to-root' });
    chartBox.prepend(svg);
    const mx = a.length - 1;
    const ymax = Math.max(1, a[mx], b[mx]) * 1.05;
    const X = (j) => M.l + (mx === 0 ? 0 : (j / mx) * (W - M.l - M.r));
    const Y = (v) => H - M.b - (v / ymax) * (H - M.t - M.b);
    const g = s('g', { class: 'grid' }, svg);
    const stepRaw = ymax / 4;
    const mag = Math.pow(10, Math.floor(Math.log10(stepRaw)));
    const step = [1, 2, 2.5, 5, 10].map((f) => f * mag).find((v) => v >= stepRaw) ?? stepRaw;
    for (let v = 0; v <= ymax; v += step) {
      s('line', { x1: M.l, x2: W - M.r, y1: Y(v), y2: Y(v) }, g);
      const tx = s('text', { x: M.l - 8, y: Y(v), 'text-anchor': 'end', dy: '0.32em', class: 'tick' }, g);
      tx.textContent = v >= 1000 ? `${fmt(v / 1000, 1)}k` : fmt(v, 0);
    }
    const xl = s('text', { x: (M.l + W - M.r) / 2, y: H - 6, 'text-anchor': 'middle', class: 'axis-label' }, svg);
    xl.textContent = 'requests served';
    for (const j of [0, mx]) {
      const tx = s('text', { x: X(j), y: H - M.b + 16, 'text-anchor': 'middle', class: 'tick' }, svg);
      tx.textContent = String(j);
    }
    const path = (vals) => vals.map((v, j) => `${j ? 'L' : 'M'}${X(j).toFixed(1)},${Y(v).toFixed(1)}`).join('');
    s('path', { d: path(b), class: 'series s2' }, svg);
    s('path', { d: path(a), class: 'series s1' }, svg);
  }
  draw();
}
