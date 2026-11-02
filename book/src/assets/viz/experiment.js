// Run splay on a request sequence and plot its cumulative cost against a
// proved bound. Each point is one instance of the theorem: the bound for the
// prefix of length j, from the same initial tree.

import * as T from './tree.js';
import { button, esc, fmt, frame, h, label, number, select } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const s = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  parent?.appendChild(e);
  return e;
};

function sequence(kind, n, m, seed) {
  const r = T.rng(seed);
  const out = [];
  let walk = Math.floor(n / 2);
  const hot = Array.from({ length: Math.max(1, Math.round(Math.log2(n))) }, () => Math.floor(r() * n));
  for (let j = 0; j < m; j++) {
    switch (kind) {
      case 'sequential': out.push(j % n); break;
      case 'repeat': out.push(Math.floor(n / 3)); break;
      case 'workingset': out.push(r() < 0.9 ? hot[Math.floor(r() * hot.length)] : Math.floor(r() * n)); break;
      case 'finger': walk = Math.max(0, Math.min(n - 1, walk + Math.round((r() - 0.5) * 4))); out.push(walk); break;
      case 'skewed': out.push(Math.min(n - 1, Math.floor(n * Math.pow(r(), 3)))); break;
      default: out.push(Math.floor(r() * n));
    }
  }
  return out;
}

const THEOREMS = {
  balance: {
    name: 'Balance (Theorem 1)',
    measure: 'total cost T = m + R',
    lean: 'Splay.Results.balance',
    bound: (n, prefix) => prefix.length * (2 + 3 * T.logb2(n)) + n * T.logb2(n),
    boundLabel: 'm(2 + 3 log₂ n) + n log₂ n',
    actual: (m, R) => m + R,
  },
  workingset: {
    name: 'Working set (Theorem 4)',
    measure: 'rotations R',
    lean: 'Splay.Results.workingSet',
    bound: (n, prefix) => 10 * T.workingSetSum(n, [], prefix) + 6 * n * (1 + T.natLog2(n)),
    boundLabel: '10·workingSetSum + 6n(1 + ⌊log₂ n⌋)',
    actual: (m, R) => R,
  },
  staticopt: {
    name: 'Static optimality, all keys used',
    measure: 'total cost T = m + R',
    lean: 'Splay.Results.staticOptimality_all_accessed',
    bound: (n, prefix) => 4 * T.staticCost(n, prefix),
    boundLabel: '4 · staticCost (only when every key occurs)',
    actual: (m, R) => m + R,
    valid: (n, prefix) => new Set(prefix).size === n,
  },
  scanning: {
    name: 'Scanning (Theorem 9)',
    measure: 'total cost T = m + R',
    lean: 'Splay.Results.scanning',
    bound: (n) => 14 * n,
    boundLabel: '14 n (for the whole scan)',
    actual: (m, R) => m + R,
    forceSequence: 'sequential',
  },
};

export default function mount(root, cfg) {
  let theorem = cfg.theorem ?? 'balance';
  let kind = cfg.sequence ?? 'uniform';
  let n = cfg.n ?? 31;
  let shape = cfg.shape ?? 'left-path';
  let m = cfg.m ?? 200;
  let seed = 7;

  const ui = frame(root, {
    title: cfg.title ?? 'Measured cost against proved bounds',
    help: ' ',
  });
  const HELP = {
    prefix: 'Each point j applies the theorem to the first j requests, from the same initial tree. The blue line is what the JavaScript port of Splay.run actually costs.',
    scan: 'The theorem bounds the whole scan 0, 1, …, n−1 by 14n. The blue line shows the cost accumulating along the scan; only its endpoint is the theorem’s left-hand side.',
  };
  const seqSel = select([['uniform', 'uniform random'], ['sequential', 'sequential scans'], ['workingset', 'small working set'], ['finger', 'local random walk'], ['skewed', 'skewed'], ['repeat', 'one key repeated']], kind, (v) => { kind = v; draw(); });
  const mInput = number(m, { min: 1, max: 2000, label: 'number of requests', onChange: (v) => { m = v; draw(); } });
  ui.controls.append(
    label('theorem', select(Object.entries(THEOREMS).map(([k, v]) => [k, v.name]), theorem, (v) => { theorem = v; draw(); })),
    label('requests', seqSel),
    label('start', select([['left-path', 'left path'], ['balanced', 'balanced'], ['random', 'random'], ['zigzag', 'zigzag']], shape, (v) => { shape = v; draw(); })),
    label('n', number(n, { min: 2, max: 255, label: 'number of keys', onChange: (v) => { n = v; draw(); } })),
    label('m', mInput),
    button('Resample', () => { seed++; draw(); }),
  );
  const chartBox = h('div', { class: 'chart' });
  ui.stage.append(chartBox);
  ui.stage.classList.add('chart-stage');
  const tooltip = h('div', { class: 'chart-tip', hidden: true });
  chartBox.append(tooltip);

  function draw() {
    const th = THEOREMS[theorem];
    const scan = th.forceSequence === 'sequential';
    seqSel.disabled = scan;
    mInput.disabled = scan;
    ui.help.textContent = scan ? HELP.scan : HELP.prefix;
    const k = th.forceSequence ?? kind;
    const mm = th.forceSequence === 'sequential' ? n : m;
    const xs = sequence(k, n, mm, seed);
    let t = T.makeTree(shape, n, seed);
    const actual = [0];
    const bound = [th.bound(n, [])];
    let R = 0;
    for (let j = 0; j < xs.length; j++) {
      const [u, c] = T.run(t, xs[j]);
      t = u; R += c;
      actual.push(th.actual(j + 1, R));
      bound.push(th.bound(n, xs.slice(0, j + 1)));
    }
    const valid = th.valid ? th.valid(n, xs) : true;
    plot(actual, bound, th, valid);
  }

  function plot(actual, bound, th, valid) {
    chartBox.querySelector('svg')?.remove();
    const W = 680; const H = 300;
    const M = { l: 52, r: 132, t: 16, b: 34 };
    const svg = s('svg', { viewBox: `0 0 ${W} ${H}`, class: 'chart-svg', role: 'img', 'aria-label': `${th.name}: measured ${th.measure} against the bound` });
    chartBox.prepend(svg);
    const mx = actual.length - 1;
    const ymax = Math.max(1, ...actual, ...bound) * 1.05;
    const X = (j) => M.l + (mx === 0 ? 0 : (j / mx) * (W - M.l - M.r));
    const Y = (v) => H - M.b - (v / ymax) * (H - M.t - M.b);
    // grid + axes
    const g = s('g', { class: 'grid' }, svg);
    const ticks = 4;
    const stepRaw = ymax / ticks;
    const mag = Math.pow(10, Math.floor(Math.log10(stepRaw)));
    const step = [1, 2, 2.5, 5, 10].map((f) => f * mag).find((v) => v >= stepRaw) ?? stepRaw;
    for (let v = 0; v <= ymax; v += step) {
      s('line', { x1: M.l, x2: W - M.r, y1: Y(v), y2: Y(v) }, g);
      const tx = s('text', { x: M.l - 8, y: Y(v), 'text-anchor': 'end', dy: '0.32em', class: 'tick' }, g);
      tx.textContent = v >= 1000 ? `${fmt(v / 1000, 1)}k` : fmt(v, 0);
    }
    const xl = s('text', { x: (M.l + W - M.r) / 2, y: H - 6, 'text-anchor': 'middle', class: 'axis-label' }, svg);
    xl.textContent = 'requests served (j)';
    for (const j of [0, mx]) {
      const tx = s('text', { x: X(j), y: H - M.b + 16, 'text-anchor': 'middle', class: 'tick' }, svg);
      tx.textContent = String(j);
    }
    const path = (vals) => vals.map((v, j) => `${j ? 'L' : 'M'}${X(j).toFixed(1)},${Y(v).toFixed(1)}`).join('');
    s('path', { d: path(bound), class: 'series s2' }, svg);
    s('path', { d: path(actual), class: 'series s1' }, svg);
    // direct labels at the line ends
    const endLabel = (vals, cls, text) => {
      const y = Y(vals[mx]);
      const gl = s('g', { class: 'end-label' }, svg);
      s('circle', { cx: X(mx), cy: y, r: 4, class: `dot ${cls}` }, gl);
      const tx = s('text', { x: X(mx) + 10, y, dy: '0.32em' }, gl);
      tx.textContent = text;
      return tx;
    };
    const ya = Y(actual[mx]); const yb = Y(bound[mx]);
    const a = endLabel(actual, 's1', `measured ${fmt(actual[mx], 0)}`);
    const b = endLabel(bound, 's2', `bound ${fmt(bound[mx], 0)}`);
    if (Math.abs(ya - yb) < 14) { a.setAttribute('y', ya + (ya > yb ? 8 : -8)); b.setAttribute('y', yb + (ya > yb ? -8 : 8)); }

    // crosshair + tooltip
    const cross = s('line', { y1: M.t, y2: H - M.b, class: 'crosshair', visibility: 'hidden' }, svg);
    const da = s('circle', { r: 4, class: 'dot s1', visibility: 'hidden' }, svg);
    const db = s('circle', { r: 4, class: 'dot s2', visibility: 'hidden' }, svg);
    const hit = s('rect', { x: M.l, y: M.t, width: W - M.l - M.r, height: H - M.t - M.b, fill: 'transparent' }, svg);
    hit.addEventListener('pointermove', (e) => {
      const r = svg.getBoundingClientRect();
      const px = ((e.clientX - r.left) / r.width) * W;
      const j = Math.max(0, Math.min(mx, Math.round(((px - M.l) / (W - M.l - M.r)) * mx)));
      for (const [el, v] of [[cross, null], [da, actual[j]], [db, bound[j]]]) {
        el.setAttribute('visibility', 'visible');
        if (v === null) { el.setAttribute('x1', X(j)); el.setAttribute('x2', X(j)); } else { el.setAttribute('cx', X(j)); el.setAttribute('cy', Y(v)); }
      }
      tooltip.hidden = false;
      tooltip.innerHTML = `<div class="tip-h">j = ${j}</div>`
        + `<div><span class="key s1"></span>measured ${esc(th.measure.split(' ')[0])} <b>${fmt(actual[j], 0)}</b></div>`
        + `<div><span class="key s2"></span>bound <b>${fmt(bound[j], 1)}</b></div>`;
      const left = (X(j) / W) * r.width;
      tooltip.style.left = `${Math.min(left + 12, r.width - 190)}px`;
      tooltip.style.top = `${(Y(Math.max(actual[j], bound[j])) / H) * r.height}px`;
    });
    hit.addEventListener('pointerleave', () => { tooltip.hidden = true; [cross, da, db].forEach((e) => e.setAttribute('visibility', 'hidden')); });

    ui.state.replaceChildren(
      h('div', { class: 'chart-legend' },
        h('span', {}, h('span', { class: 'key s1' }), `measured ${th.measure}`),
        h('span', {}, h('span', { class: 'key s2' }), `bound: ${th.boundLabel}`)),
      h('div', { class: 'vnote', html: valid
        ? `Theorem: <code>${esc(th.lean)}</code>. Final ratio measured / bound = ${fmt(actual[mx] / Math.max(1e-9, bound[mx]), 3)}.`
        : `<span class="vno">Hypothesis not met:</span> not every key occurs in this sequence, so <code>${esc(th.lean)}</code> does not apply (the curve is shown for comparison only).` }),
    );
  }
  draw();
}
