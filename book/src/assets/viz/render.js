// SVG drawing of shapes. A node's horizontal position is its inorder rank, so
// rotations (which preserve inorder) move nodes only vertically: the figure
// itself shows that keys keep their order.

import { layout, size, height } from './tree.js';

const SVG = 'http://www.w3.org/2000/svg';
const el = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (parent) parent.appendChild(e);
  return e;
};

const ease = (t) => (t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2);

export class TreeView {
  /**
   * opts: { dx, dy, r, label(key) -> string, onNode(key, event), onGap(gap, parentKey, side),
   *         showGaps: bool, minWidth }
   */
  constructor(parent, opts = {}) {
    this.opts = { dx: 38, dy: 46, r: 14, pad: 22, ...opts };
    this.wrap = document.createElement('div');
    this.wrap.className = 'tv';
    parent.appendChild(this.wrap);
    this.svg = el('svg', { class: 'tv-svg', role: 'img' }, this.wrap);
    this.gEdges = el('g', { class: 'tv-edges' }, this.svg);
    this.gGaps = el('g', { class: 'tv-gaps' }, this.svg);
    this.gNodes = el('g', { class: 'tv-nodes' }, this.svg);
    this.pos = new Map(); // key -> {x, y}
    this.nodes = new Map(); // key -> <g>
    this.anim = null;
    this.tree = undefined;
  }

  geometry(tree) {
    const n = size(tree);
    const { pad, r } = this.opts;
    const dx = n > 24 ? Math.max(20, this.opts.dx * 24 / n) : this.opts.dx;
    const dy = this.opts.dy;
    const h = Math.max(1, height(tree));
    const width = Math.max(this.opts.minWidth ?? 0, pad * 2 + Math.max(0, n - 1) * dx + 2 * r);
    const extra = this.opts.showGaps ? dy * 0.75 : 0;
    const heightPx = pad * 2 + (h - 1) * dy + 2 * r + extra;
    const offsetX = (width - (Math.max(0, n - 1) * dx)) / 2;
    return { n, dx, dy, width, height: heightPx, x: (k) => offsetX + k * dx, y: (d) => pad + r + d * dy };
  }

  update(tree, { animate = true, classes = new Map(), labels = null, edgeClasses = new Map() } = {}) {
    const g = this.geometry(tree);
    this.geom = g;
    this.svg.setAttribute('viewBox', `0 0 ${g.width} ${g.height}`);
    this.svg.style.maxWidth = `${g.width}px`;
    const nodes = layout(tree);
    const target = new Map(nodes.map((v) => [v.key, { x: g.x(v.key), y: g.y(v.depth) }]));
    const label = labels ?? this.opts.label ?? ((k) => String(k));

    // Nodes: reuse elements by key (rank).
    for (const [key, e] of this.nodes) if (!target.has(key)) { e.remove(); this.nodes.delete(key); this.pos.delete(key); }
    for (const v of nodes) {
      let e = this.nodes.get(v.key);
      if (!e) {
        e = el('g', { class: 'tv-node', tabindex: '0' }, this.gNodes);
        el('circle', { r: this.opts.r }, e);
        el('text', { 'text-anchor': 'middle', dy: '0.35em' }, e);
        e.addEventListener('click', (ev) => this.opts.onNode?.(Number(e.dataset.key), ev));
        e.addEventListener('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); this.opts.onNode?.(Number(e.dataset.key), ev); } });
        e.addEventListener('mouseenter', () => this.opts.onHover?.(Number(e.dataset.key)));
        e.addEventListener('mouseleave', () => this.opts.onHover?.(null));
        this.nodes.set(v.key, e);
        const p = target.get(v.key);
        this.pos.set(v.key, { x: p.x, y: animate && this.tree !== undefined ? p.y - 20 : p.y });
      }
      e.dataset.key = v.key;
      const text = label(v.key);
      e.querySelector('text').textContent = text;
      e.querySelector('text').setAttribute('class', text.length > 2 ? 'small' : '');
      e.setAttribute('class', `tv-node ${classes.get(v.key) ?? ''} ${this.opts.onNode ? 'clickable' : ''}`);
      e.setAttribute('aria-label', `key ${text}`);
    }

    // Edges and gaps are redrawn every frame from node positions.
    this.edges = nodes.filter((v) => v.parent !== null).map((v) => ({ from: v.parent, to: v.key, cls: edgeClasses.get(v.key) ?? '' }));
    this.gaps = [];
    if (this.opts.showGaps) {
      // Each empty subtree sits in the inorder gap between two ranks.
      const walk = (s, lo, d, parentKey, side) => {
        if (s === null) { this.gaps.push({ gap: lo, depth: d, parentKey, side }); return; }
        const k = lo + size(s[0]);
        walk(s[0], lo, d + 1, k, 'left');
        walk(s[1], k + 1, d + 1, k, 'right');
      };
      walk(tree, 0, 0, null, null);
    }
    this.tree = tree;
    const from = new Map([...this.pos].map(([k, p]) => [k, { ...p }]));
    cancelAnimationFrame(this.anim);
    const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;
    if (!animate || reduce) { this.frame(target, target, 1); return Promise.resolve(); }
    return new Promise((resolve) => {
      const start = performance.now();
      const dur = this.opts.duration ?? 420;
      const step = (now) => {
        const t = Math.min(1, (now - start) / dur);
        this.frame(from, target, ease(t));
        if (t < 1) this.anim = requestAnimationFrame(step); else resolve();
      };
      this.anim = requestAnimationFrame(step);
    });
  }

  frame(from, to, t) {
    for (const [key, p] of to) {
      const a = from.get(key) ?? p;
      const x = a.x + (p.x - a.x) * t;
      const y = a.y + (p.y - a.y) * t;
      this.pos.set(key, { x, y });
      this.nodes.get(key)?.setAttribute('transform', `translate(${x.toFixed(2)},${y.toFixed(2)})`);
    }
    this.gEdges.replaceChildren();
    for (const e of this.edges) {
      const a = this.pos.get(e.from); const b = this.pos.get(e.to);
      if (a && b) el('line', { x1: a.x, y1: a.y, x2: b.x, y2: b.y, class: `tv-edge ${e.cls}` }, this.gEdges);
    }
    this.gGaps.replaceChildren();
    if (this.opts.showGaps && t === 1) {
      const g = this.geom;
      for (const gap of this.gaps) {
        const parent = gap.parentKey === null ? null : this.pos.get(gap.parentKey);
        const x = g.x(gap.gap - 0.5);
        const y = parent ? parent.y + g.dy * 0.72 : g.y(0);
        if (parent) el('line', { x1: parent.x, y1: parent.y, x2: x, y2: y, class: 'tv-gap-edge' }, this.gGaps);
        const s = el('rect', { x: x - 6, y: y - 6, width: 12, height: 12, rx: 2, class: `tv-gap ${this.opts.onGap ? 'clickable' : ''} ${this.gapClass?.(gap.gap) ?? ''}`, tabindex: this.opts.onGap ? '0' : '-1' }, this.gGaps);
        const title = el('title', {}, s);
        title.textContent = `empty subtree in gap ${gap.gap} (between ranks ${gap.gap - 1} and ${gap.gap})`;
        if (this.opts.onGap) {
          s.addEventListener('click', () => this.opts.onGap(gap.gap, gap.parentKey, gap.side));
          s.addEventListener('keydown', (ev) => { if (ev.key === 'Enter') this.opts.onGap(gap.gap, gap.parentKey, gap.side); });
        }
      }
    }
  }
}
