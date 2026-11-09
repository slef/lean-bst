// A map of the models of Part I and the simulations between them. An arrow
// A → B means that an execution (or an online algorithm) in model A gives one
// in model B serving the same requests, at the cost written on the arrow.
//
// Dashed boxes and arrows (`todo`) are models and simulations that are not
// formalized yet; they point to the roadmap.
//
// As in the map of the bounds, theorem links are not hard-coded: the figure
// borrows the href of a link to each declaration found elsewhere on the page
// (the table under it), so the book build checks them.

import { esc, frame, h } from './ui.js';

const SVG = 'http://www.w3.org/2000/svg';
const s = (name, attrs = {}, parent) => {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  parent?.appendChild(e);
  return e;
};
const L = 'RotationBST.';
const W = 860, H = 540, BW = 168, BH = 50;

const NODES = [
  { id: 'MF', x: 100, y: 70, sym: 'Many fingers', name: 'K: instructions + requests', href: 'fingers.html',
    text: 'Several persistent fingers in one tree; each moves or rotates at its node, and a request is served when some finger stands on it.' },
  { id: 'PTR', x: 430, y: 70, sym: 'Pointer machine', name: 'K: instructions + requests', href: 'pointer.html',
    text: 'One cursor, starting at the root for every request, that moves along edges and rotates its node over its parent.' },
  { id: 'LS', x: 760, y: 70, sym: 'Linked searches', name: 'not a BST', href: 'linked-search.html', alone: true,
    text: 'Static searches in a store of many small trees joined by links, with an explicit count of memory words. Used only by the multiple-tree structure; it is not compared with the other models.' },
  { id: 'ROT', x: 100, y: 230, sym: 'Rotations', name: 'm + R', href: 'accesses.html',
    text: 'Root accesses on shapes whose keys are the inorder ranks: each request rotates anywhere until the requested key is at the root. The basic model of the library.' },
  { id: 'ASS', x: 760, y: 230, sym: 'Geometric view', name: '|E|: points', href: 'geometry.html',
    text: 'Arborally satisfied point sets containing the request points (key, time).' },
  { id: 'LAB', x: 100, y: 350, sym: 'Labelled trees', name: 'm + R', href: 'keys.html',
    text: 'The rotation model on trees that store arbitrary ordered keys.' },
  { id: 'REG', x: 760, y: 350, sym: 'Touched regions', name: 'touched nodes', href: 'regions.html',
    text: 'Each request touches a rooted subtree containing the requested key and rearranges it; the cost is the number of touched nodes.' },
  { id: 'DIC', x: 430, y: 350, sym: 'Insertions, deletions', name: 'm + search + R', href: 'dictionary.html', todo: true,
    text: 'Dictionaries: insertions and deletions by rank, each charged its search path plus its rotations, with balance data in the nodes. Only the splay-tree version is formalized.' },
  { id: 'ONP', x: 100, y: 490, sym: 'Online pointer', name: 'algorithms', href: 'pointer.html#running-an-online-algorithm-on-the-pointer-machine',
    text: 'Online algorithms on the pointer machine: each response depends only on the requests so far.' },
  { id: 'ONR', x: 430, y: 490, sym: 'Online rotation', name: 'algorithms', href: 'online.html',
    text: 'Online algorithms in the rotation model, the Algorithm structure of Part III. A run is an execution of the rotation model.' },
  { id: 'ONG', x: 760, y: 490, sym: 'Online geometric', name: 'algorithms', href: 'geometry.html#online-algorithms',
    text: 'Rules that add one row of points per request, looking only at the rows before it.' },
];

const EDGES = [
  { from: 'MF', to: 'PTR', off: -6, label: '1 finger: K ≤ 464·cost', lab: [265, 52, 'middle'], thms: ['LazyFinger.Dynamic.Results.same_tree'],
    text: 'A static tree searched with a lazy finger is a one-finger execution, and from the same tree some pointer execution costs at most 464 times as much. For k fingers the library proves a factor 344 + 60(k + 1) in a proof file, outside the reading interface.' },
  { from: 'PTR', to: 'MF', off: -6, label: 'traces are 1-finger traces', lab: [265, 106, 'middle'], thms: [],
    text: 'Every pointer trace is a one-finger trace with the same instructions (proved in a proof file, outside the reading interface). Requests differ: a finger is never sent back to the root.' },
  { from: 'ROT', to: 'PTR', off: -6, label: 'K + 32d ≤ 32R + 17m', lab: [250, 138, 'end'], thms: ['Pointer.Results.to_pointer_lazy', 'Pointer.Results.to_pointer'],
    text: 'A rotation execution becomes a pointer execution serving the same requests from the same tree, ending d rotations away from the same final tree. Exactly the same final tree is reachable at cost K ≤ m + 2nR.' },
  { from: 'PTR', to: 'ROT', off: -6, label: 'm + R + q ≤ 3K', lab: [282, 172, 'start'], thms: ['Pointer.Results.to_rotations'],
    text: 'A pointer execution becomes a rotation execution serving the same requests from the same tree, ending q rotations away from its final tree.' },
  { from: 'PTR', to: 'ASS', off: -6, label: '|E| ≤ 6K', lab: [610, 138, 'start'], thms: ['Geometric.Equivalence.Results.pointers_to_ass'],
    text: 'The touched points of a pointer execution, completed, form a geometric solution. The initial tree is forgotten.' },
  { from: 'ASS', to: 'PTR', off: -6, label: 'K ≤ 64n + 3168|E|', lab: [578, 172, 'end'], thms: ['Geometric.Equivalence.Results.ass_to_pointers_from', 'Geometric.Equivalence.Results.ass_to_pointers'],
    text: 'A geometric solution becomes a pointer execution from any prescribed initial tree. If the initial tree may be chosen, K ≤ 33|E|.' },
  { from: 'ROT', to: 'ASS', off: -6, label: '|E| ≤ 2R + m', lab: [430, 214, 'middle'], thms: ['Geometric.Equivalence.Results.rotations_to_ass'],
    text: 'The touched points of a rotation execution form a geometric solution. The initial tree is forgotten.' },
  { from: 'ASS', to: 'ROT', off: -6, label: 'm + R ≤ 2n + 99|E|', lab: [430, 256, 'middle'], thms: ['Geometric.Equivalence.Results.ass_to_rotations'],
    text: 'A geometric solution becomes a rotation execution from every initial tree.' },
  { from: 'LAB', to: 'ROT', both: true, label: 'equal', lab: [110, 294, 'start'], thms: ['Representation.execution_on_keys_iff'],
    text: 'Labelled executions and executions on shapes correspond exactly, with the same number of rotations.' },
  { from: 'REG', to: 'ASS', both: true, label: 'equal', lab: [770, 294, 'start'], thms: ['Geometric.Equivalence.Results.ass_iff_region_execution'],
    text: 'A point set is arborally satisfied exactly when it is the touch set of a region execution from a suitable initial tree, at the same cost.' },
  { from: 'ROT', to: 'DIC', todo: true, label: 'accesses only: ≤ 2(m + R)', lab: [255, 350, 'middle'], thms: [],
    text: 'A rotation execution is a dictionary execution without insertions or deletions. Its search paths cost at most m + R in total, because each rotation raises the requested key by at most one level.' },
  { from: 'ONR', to: 'ONP', label: 'K + 32d ≤ 32R + 17m', lab: [265, 480, 'middle'], thms: ['Pointer.Lazy.Online.Results.simulation'],
    text: 'Every online rotation algorithm runs online on the pointer machine, from any initial tree, with the same bound as offline.' },
  { from: 'ONG', to: 'ONR', label: 'R ≤ 6018(points + n)', lab: [595, 480, 'middle'], thms: ['Geometric.Equivalence.Results.online_bst'],
    text: 'Every online geometric algorithm is simulated by an online rotation algorithm, from any initial tree.' },
];

function hrefFor(name) {
  const suffix = `#decl-${L}${name}`;
  for (const a of document.querySelectorAll('a[href]')) {
    if (a.closest('.viz')) continue;
    if (a.getAttribute('href').endsWith(suffix)) return a.getAttribute('href');
  }
  return null;
}

function clip(n, tx, ty) {
  const dx = tx - n.x, dy = ty - n.y;
  const sx = dx ? (BW / 2 + 4) / Math.abs(dx) : Infinity;
  const sy = dy ? (BH / 2 + 4) / Math.abs(dy) : Infinity;
  const k = Math.min(sx, sy);
  return [n.x + dx * k, n.y + dy * k];
}

export default function mount(root, cfg = {}) {
  const roadmap = cfg.roadmap || null;
  const pending = ` <em>Not formalized yet</em>${roadmap ? `; see the <a href="${esc(roadmap)}">roadmap</a>` : ''}.`;
  const ui = frame(root, {
    title: 'How the models relate',
    help: 'An arrow A → B means that an execution in model A gives one in model B serving the same requests, at the cost written on it: m requests, R rotations, K pointer instructions plus requests, |E| points, n keys. A double arrow is an exact correspondence. Dashed grey boxes and arrows are not formalized yet. Hover over a model or an arrow for details; click to open its chapter or theorem.',
  });
  const byId = Object.fromEntries(NODES.map((n) => [n.id, n]));
  const svg = s('svg', { viewBox: `0 0 ${W} ${H}`, class: 'bounds-map', role: 'img', 'aria-label': 'How the models relate' }, ui.stage);
  const defs = s('defs', {}, svg);
  for (const [id, cls] of [['head', 'bm-head'], ['hot', 'bm-head hot'], ['todo', 'bm-head todo']]) {
    const m = s('marker', { id: `mm-${id}`, viewBox: '0 0 10 10', refX: 9, refY: 5, markerWidth: 7, markerHeight: 7, orient: 'auto-start-reverse' }, defs);
    s('path', { d: 'M0,0 L10,5 L0,10 z', class: cls }, m);
  }
  s('line', { x1: 20, y1: 420, x2: W - 20, y2: 420, class: 'mm-band' }, svg);
  s('text', { x: 24, y: 412, class: 'mm-band-label' }, svg).textContent = 'executions';
  s('text', { x: 24, y: 438, class: 'mm-band-label' }, svg).textContent = 'online algorithms';

  const caption = h('div', { class: 'bm-caption' });
  ui.state.append(caption);
  const idle = 'Hover over a model or an arrow.';
  caption.textContent = idle;
  const link = (names) => names.map((n) => {
    const href = hrefFor(n);
    return href ? `<a href="${esc(href)}"><code>${esc(n)}</code></a>` : `<code>${esc(n)}</code>`;
  }).join(', ');

  const edgeEls = [];
  for (const e of EDGES) {
    const a = byId[e.from], b = byId[e.to];
    let [x1, y1] = clip(a, b.x, b.y), [x2, y2] = clip(b, a.x, a.y);
    if (e.off) {
      const len = Math.hypot(x2 - x1, y2 - y1), ox = -(y2 - y1) / len * e.off, oy = (x2 - x1) / len * e.off;
      x1 += ox; x2 += ox; y1 += oy; y2 += oy;
    }
    const head = e.todo ? 'url(#mm-todo)' : 'url(#mm-head)';
    const g = s('g', { class: `bm-edge imp${e.todo ? ' todo' : ''}`, tabindex: 0 }, svg);
    s('line', { x1, y1, x2, y2, class: 'bm-hit' }, g);
    const line = s('line', { x1, y1, x2, y2, class: 'bm-line', 'marker-end': head }, g);
    if (e.both) line.setAttribute('marker-start', 'url(#mm-head)');
    const [tx, ty, anchor] = e.lab;
    s('text', { x: tx, y: ty, class: 'bm-label', 'text-anchor': anchor }, g).textContent = e.label;
    const show = () => {
      clear();
      g.classList.add('hot');
      line.setAttribute('marker-end', 'url(#mm-hot)');
      if (e.both) line.setAttribute('marker-start', 'url(#mm-hot)');
      const rel = e.both ? '↔' : '→';
      const thms = e.todo ? pending : e.thms.length ? ` <span class="bm-thm">${link(e.thms)}</span>` : '';
      caption.innerHTML = `<strong>${esc(a.sym)} ${rel} ${esc(b.sym)}: ${esc(e.label)}.</strong> ${esc(e.text)}${thms}`;
      for (const [id, el] of nodeEls) el.classList.toggle('dim', id !== e.from && id !== e.to);
      for (const o of edgeEls) o.g.classList.toggle('dim', o.e !== e);
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => {
      const href = e.todo ? roadmap : e.thms.length && hrefFor(e.thms[0]);
      if (href) location.href = href;
    });
    edgeEls.push({ e, g, line, head });
  }

  const nodeEls = new Map();
  for (const n of NODES) {
    const g = s('g', { class: `bm-node${n.alone || n.todo ? ' lower' : ''}${n.todo ? ' todo-model' : ''}`, tabindex: 0 }, svg);
    s('rect', { x: n.x - BW / 2, y: n.y - BH / 2, width: BW, height: BH, rx: 8 }, g);
    s('text', { x: n.x, y: n.y - 3, class: 'bm-sym', 'text-anchor': 'middle' }, g).textContent = n.sym;
    s('text', { x: n.x, y: n.y + 15, class: 'bm-name', 'text-anchor': 'middle' }, g).textContent = n.name;
    const show = () => {
      clear();
      const mine = EDGES.filter((e) => e.from === n.id || e.to === n.id);
      const near = new Set(mine.flatMap((e) => [e.from, e.to]));
      for (const [id, el] of nodeEls) {
        el.classList.toggle('focus', id === n.id);
        el.classList.toggle('dim', !near.has(id));
      }
      for (const o of edgeEls) o.g.classList.toggle('dim', !mine.includes(o.e));
      const out = mine.map((e) => {
        const other = byId[e.from === n.id ? e.to : e.from];
        const dir = e.both ? '↔' : e.from === n.id ? '→' : '←';
        return `${dir} ${esc(other.sym)} (${esc(e.label)})`;
      });
      caption.innerHTML = `<strong>${esc(n.sym)}.</strong> ${esc(n.text)}${n.todo ? pending : ''}${out.length ? ` Relations: ${out.join('; ')}.` : ''} <a href="${esc(n.href)}">Open its chapter.</a>`;
    };
    g.addEventListener('mouseenter', show);
    g.addEventListener('focus', show);
    g.addEventListener('click', () => { location.href = n.href; });
    nodeEls.set(n.id, g);
  }
  svg.addEventListener('mouseleave', () => { clear(); caption.textContent = idle; });

  function clear() {
    for (const el of nodeEls.values()) el.classList.remove('focus', 'dim');
    for (const { e, g, line, head } of edgeEls) {
      g.classList.remove('hot', 'dim');
      line.setAttribute('marker-end', head);
      if (e.both) line.setAttribute('marker-start', 'url(#mm-head)');
    }
  }
}
