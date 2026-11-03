// A balanced 2–3–4 tree, its binary representation (`Multiway.binary`) and its
// minimum-finger comparison tree (`Finger.binaryView`), drawn with x = rank in
// all three panels. Selecting a rank shows the finger ascent
// (`searchLevels`, `nearSearchLevels`) and the search depths in both binary trees.

import * as T from './tree.js';
import * as M from './multiway.js';
import { TreeView } from './render.js';
import { button, frame, h, label, mono, row, select } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const el = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (parent) parent.appendChild(e);
  return e;
};

const CSS = `
.st-panels { display: grid; gap: .5rem; width: 100%; }
.st-panel { display: flex; flex-direction: column; align-items: center; }
.st-label { align-self: flex-start; font-size: .72rem; color: var(--fg-faint); font-family: var(--sans); }
.st-label code { font-size: .72rem; }
.mw-svg { width: 100%; height: auto; overflow: visible; }
.mw-node rect { fill: var(--bg); stroke: var(--accent); stroke-width: 1.6; }
.mw-node.spine rect { fill: var(--violet-soft); stroke: var(--violet); }
.mw-node.climbed rect { fill: var(--violet-soft); stroke: var(--violet); stroke-width: 2.6; }
.mw-node.holds rect { fill: var(--target-soft); stroke: var(--target); stroke-width: 2.4; }
.mw-key { cursor: pointer; }
.mw-key text { font-family: var(--mono); font-size: 11px; fill: var(--fg); pointer-events: none; }
.mw-key circle { fill: transparent; stroke: none; }
.mw-key:hover circle { fill: var(--accent-soft); }
.mw-key.target circle { fill: var(--target); }
.mw-key.target text { fill: var(--bg); font-weight: 700; }
.mw-edge { stroke: var(--fg-faint); stroke-width: 1.4; fill: none; }
.mw-edge.climbed { stroke: var(--violet); stroke-width: 2.4; }
.tv-node.spine circle { stroke: var(--violet); fill: var(--violet-soft); }
`;
let styled = false;

function geometry(n, { dx0 = 34, r = 12, pad = 18, dy = 44, depth = 1 } = {}) {
  const dx = n > 24 ? Math.max(20, dx0 * 24 / n) : dx0;
  const width = pad * 2 + Math.max(0, n - 1) * dx + 2 * r;
  const offsetX = (width - Math.max(0, n - 1) * dx) / 2;
  return { dx, dy, r, width, height: pad * 2 + (depth - 1) * dy + 2 * r, x: (k) => offsetX + k * dx, y: (d) => pad + r + d * dy };
}

/** Draw a 2–3–4 tree with x = rank; returns nothing, wires clicks to onKey. */
function drawMultiway(svg, t, { onKey, target, spineIds, climbedIds, holdsId, climbedEdges }) {
  svg.replaceChildren();
  const n = M.size(t);
  const nodes = M.layoutMultiway(t);
  const depth = Math.max(1, ...nodes.map((v) => v.depth + 1));
  const g = geometry(n, { depth });
  svg.setAttribute('viewBox', `0 0 ${g.width} ${g.height}`);
  svg.style.maxWidth = `${g.width}px`;
  const gEdges = el('g', {}, svg);
  const gNodes = el('g', {}, svg);
  const box = new Map();
  for (const v of nodes) {
    const x0 = g.x(v.keys[0]) - g.r;
    const x1 = g.x(v.keys[v.keys.length - 1]) + g.r;
    box.set(v.id, { x0, x1, y: g.y(v.depth), v });
  }
  for (const v of nodes) {
    if (v.parent === null) continue;
    const p = box.get(v.parent);
    const c = box.get(v.id);
    // The child's position among its siblings decides which gap it leaves from.
    const sib = nodes.filter((u) => u.parent === v.parent);
    const i = sib.indexOf(v);
    const keys = p.v.keys;
    const ax = i === 0 ? g.x(keys[0]) - g.r * 0.7
      : i === keys.length ? g.x(keys[keys.length - 1]) + g.r * 0.7
        : (g.x(keys[i - 1]) + g.x(keys[i])) / 2;
    const cls = climbedEdges.has(v.id) ? 'mw-edge climbed' : 'mw-edge';
    el('line', { x1: ax, y1: p.y + g.r, x2: (c.x0 + c.x1) / 2, y2: c.y - g.r, class: cls }, gEdges);
  }
  for (const { x0, x1, y, v } of box.values()) {
    let cls = 'mw-node';
    if (spineIds.has(v.id)) cls += ' spine';
    if (climbedIds.has(v.id)) cls += ' climbed';
    if (v.id === holdsId) cls += ' holds';
    const gn = el('g', { class: cls }, gNodes);
    el('rect', { x: x0, y: y - g.r, width: x1 - x0, height: 2 * g.r, rx: g.r }, gn);
    for (const k of v.keys) {
      const gk = el('g', { class: `mw-key${k === target ? ' target' : ''}`, tabindex: '0', transform: `translate(${g.x(k)},${y})` }, gn);
      el('circle', { r: g.r - 2.5 }, gk);
      const tx = el('text', { 'text-anchor': 'middle', dy: '0.35em' }, gk);
      tx.textContent = String(k);
      gk.addEventListener('click', () => onKey(k));
      gk.addEventListener('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); onKey(k); } });
    }
  }
}

/** Ids of the multiway nodes on the left (or right) spine, bottom first. */
function spineOf(nodes, side) {
  const ids = [];
  let cur = nodes.find((v) => v.parent === null);
  while (cur) {
    ids.unshift(cur.id);
    const kids = nodes.filter((u) => u.parent === cur.id);
    cur = kids.length ? (side === 'left' ? kids[0] : kids[kids.length - 1]) : null;
  }
  return ids;
}

function pathKeys(t, x) {
  const path = T.pathTo(t, x) ?? [];
  const keys = [];
  let s = t; let lo = 0;
  for (const d of path) {
    const k = lo + T.size(s[0]);
    keys.push(k);
    if (d === 'L') s = s[0]; else { lo = k + 1; s = s[1]; }
  }
  return keys;
}

export default function mount(root, cfg) {
  if (!styled) { document.head.append(h('style', {}, CSS)); styled = true; }
  let height = cfg.height ?? 3;
  let seed = cfg.seed ?? 5;
  let tree = cfg.tree ?? M.randomMultiway(height, T.rng(seed));
  let rank = cfg.rank ?? Math.min(M.size(tree) - 1, 5);
  let mode = cfg.mode ?? 'min';

  const ui = frame(root, {
    title: cfg.title ?? 'A 2–3–4 tree, its binary form, and its minimum finger',
    help: 'Click any key to select its rank. Violet: the spine the finger climbs (searchLevels); orange: the selected key and the search paths to it in the two binary trees. All three panels place a key at the same horizontal position, its rank.',
  });
  const panels = h('div', { class: 'st-panels' });
  ui.stage.append(panels);
  const mkPanel = (html) => {
    const p = h('div', { class: 'st-panel' }, h('div', { class: 'st-label', html }));
    panels.append(p);
    return p;
  };
  const pm = mkPanel('2–3–4 tree <code>t : Multiway</code>');
  const svg = el('svg', { class: 'mw-svg', role: 'img', 'aria-label': '2–3–4 tree' }, pm);
  const pb = mkPanel('its binary representation <code>t.binary</code>');
  const pv = mkPanel('the minimum-finger view <code>(binaryView t).tree</code>');
  const opts = { dx: 34, r: 12, dy: 40, pad: 18, onNode: (k) => { rank = k; draw(); } };
  const vb = new TreeView(pb, opts);
  const vv = new TreeView(pv, opts);

  ui.controls.append(
    label('height', select([[2, '2'], [3, '3']], height, (v) => { height = Number(v); fresh(); })),
    label('finger', select([['min', 'minimum'], ['near', 'nearer end']], mode, (v) => { mode = v; draw(); })),
    button('New tree', () => { seed = Math.floor(Math.random() * 1e6); fresh(); }),
  );

  function fresh() {
    tree = M.randomMultiway(height, T.rng(seed));
    rank = Math.min(rank, M.size(tree) - 1);
    draw();
  }

  function draw() {
    const n = M.size(tree);
    const hgt = M.balancedHeight(tree);
    const bin = M.binary(tree);
    const view = M.binaryView(tree);
    const vt = M.viewTree(view);
    const nodes = M.layoutMultiway(tree);
    const other = n - 1 - rank;
    const fromMax = mode === 'near' && rank > other;
    const levels = mode === 'near' ? M.nearSearchLevels(tree, rank) : M.searchLevels(tree, rank);
    const spine = spineOf(nodes, fromMax ? 'right' : 'left');
    const climbed = new Set(spine.slice(0, levels));
    const holds = nodes.find((v) => v.keys.includes(rank))?.id;
    const climbedEdges = new Set(spine.slice(0, Math.max(0, levels - 1)));
    drawMultiway(svg, tree, { onKey: (k) => { rank = k; draw(); }, target: rank, spineIds: new Set(spine), climbedIds: climbed, holdsId: holds, climbedEdges });

    const hl = (t, extra = new Map()) => {
      const classes = new Map(extra);
      const edges = new Map();
      for (const k of pathKeys(t, rank)) classes.set(k, 'path');
      const p = T.pathTo(t, rank) ?? [];
      // Edges are keyed by their lower endpoint: every node on the path below the root.
      let s = t; let lo = 0;
      for (const d of p) {
        const k = lo + T.size(s[0]);
        if (d === 'L') s = s[0]; else { lo = k + 1; s = s[1]; }
        edges.set(lo + T.size(s[0]), 'path');
      }
      classes.set(rank, 'target');
      return { classes, edgeClasses: edges, animate: false };
    };
    const spineKeys = new Map();
    { let s = vt; let lo = 0; for (let i = 0; i < view.spine.length; i++) { const k = lo + T.size(s[0]); spineKeys.set(k, 'spine'); lo = k + 1; s = s[1]; } }
    vb.update(bin, hl(bin));
    vv.update(vt, hl(vt, spineKeys));

    const lg = T.natLog2;
    const dBin = T.depth(bin, rank);
    const dView = T.depth(vt, rank);
    const splayCost = T.run(vt, rank)[1];
    ui.state.replaceChildren(
      row('t.size, height h', `${n} keys, h = ${hgt}, ${M.nodes(tree)} multiway nodes`),
      row('viewCost t', `${M.viewCost(tree)} rotation${M.viewCost(tree) === 1 ? '' : 's'} ≤ 3 · size = ${3 * n} <span class="vnote">(finger_construction)</span>`),
      row('spine length', `${view.spine.length} ≤ 3h = ${3 * hgt} <span class="vnote">(the comb of the view: rank 0 and the separators below it, violet)</span>`),
      row('selected rank', mono(String(rank))),
      row(mode === 'near' ? 'nearSearchLevels' : 'searchLevels', mode === 'near'
        ? `${levels} ≤ ⌊log₂(min(${rank}, ${other}) + 1)⌋ + 1 = ${lg(Math.min(rank, other) + 1) + 1} <span class="vnote">(nearer_endpoint; climbing from the ${fromMax ? 'maximum' : 'minimum'})</span>`
        : `${levels} multiway levels climbed from the minimum`),
      row('depth in t.binary', `${dBin} <span class="vnote">(searching from the root)</span>`),
      row('depth in the view', `${dView} ≤ 5⌊log₂(${rank} + 1)⌋ + 6 = ${5 * lg(rank + 1) + 6} <span class="vnote">(finger_search_depth; splaying it costs ${splayCost} rotations, finger_access)</span>`),
    );
  }
  draw();
}
