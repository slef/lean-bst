// JavaScript transcriptions of the executable Lean definitions.
//
// Each function mirrors one Lean definition, equation by equation, and keeps its
// name. test/port.test.mjs checks them against values computed by Lean itself
// (book/lean/Export.lean), so the figures run the library's algorithms, not
// look-alikes.
//
// A Tree is `null` (Tree.nil) or a two-element array `[left, right]`
// (Tree.node left right). Trees are never mutated.

export const nil = null;
export const node = (l, r) => [l, r];
export const isNode = (t) => t !== null;

const sizes = new WeakMap();
/** Tree.size */
export function size(t) {
  if (t === null) return 0;
  let s = sizes.get(t);
  if (s === undefined) { s = size(t[0]) + 1 + size(t[1]); sizes.set(t, s); }
  return s;
}

export function equal(s, t) {
  if (s === null || t === null) return s === t;
  return equal(s[0], t[0]) && equal(s[1], t[1]);
}

// --- Pointer.Frame, plug, offset (Pointer/Machine/Abstract) -----------------

/** Frame.left r: the cursor is in the left child; `r` is the parent's other child. */
export const left = (tree) => ({ side: 'left', tree });
/** Frame.right l: the cursor is in the right child; `l` is the parent's other child. */
export const right = (tree) => ({ side: 'right', tree });

/** Pointer.plug: reassemble the whole tree from a focus and its ancestors. */
export function plug(cs, t) {
  let out = t;
  for (const f of cs) out = f.side === 'left' ? node(out, f.tree) : node(f.tree, out);
  return out;
}

/** Pointer.offset: number of keys before the focused subtree. */
export function offset(cs) {
  let o = 0;
  for (const f of cs) if (f.side === 'right') o += size(f.tree) + 1;
  return o;
}

/** Config.key?: the inorder rank of the node under the cursor, or null. */
export function keyOf(config) {
  if (config.focus === null) return null;
  return offset(config.context) + size(config.focus[0]);
}

// --- Splay (Splay/Algorithm/Abstract) ----------------------------------------

/** Splay.locate: ordinary rank search, nearest ancestor first in the context. */
export function locate(t, x) {
  if (t === null) return { focus: null, context: [] };
  const [l, r] = t;
  if (x < size(l)) {
    const c = locate(l, x);
    return { focus: c.focus, context: [...c.context, left(r)] };
  }
  if (x === size(l)) return { focus: t, context: [] };
  const c = locate(r, x - size(l) - 1);
  return { focus: c.focus, context: [...c.context, right(l)] };
}

/**
 * One equation of Splay.splayAt. Returns {equation, l, r, context} for the
 * recursive call, or {equation, result} for a base case. Equations are
 * numbered 1–7 in source order.
 */
export function splayStep(l, r, cs) {
  if (cs.length === 0) return { equation: 1, case: 'done', result: node(l, r) };
  const [f, g, ...rest] = cs;
  if (cs.length === 1) {
    if (f.side === 'left') return { equation: 2, case: 'zig', result: node(l, node(r, f.tree)) };
    return { equation: 3, case: 'zig', result: node(node(f.tree, l), r) };
  }
  if (f.side === 'left' && g.side === 'left') {
    const b = f.tree, c = g.tree;
    return { equation: 4, case: 'zig-zig', l, r: node(r, node(b, c)), context: rest };
  }
  if (f.side === 'right' && g.side === 'right') {
    const a = f.tree, b = g.tree;
    return { equation: 5, case: 'zig-zig', l: node(node(b, a), l), r, context: rest };
  }
  if (f.side === 'right' && g.side === 'left') {
    const a = f.tree, b = g.tree;
    return { equation: 6, case: 'zig-zag', l: node(a, l), r: node(r, b), context: rest };
  }
  const b = f.tree, a = g.tree; // .left b :: .right a :: cs
  return { equation: 7, case: 'zig-zag', l: node(a, l), r: node(r, b), context: rest };
}

/** Splay.splayAt */
export function splayAt(l, r, cs) {
  for (;;) {
    const s = splayStep(l, r, cs);
    if ('result' in s) return s.result;
    ({ l, r, context: cs } = s);
  }
}

/** Splay.run: the splayed tree and its exact rotation count. */
export function run(t, x) {
  const c = locate(t, x);
  if (c.focus === null) return [t, 0];
  return [splayAt(c.focus[0], c.focus[1], c.context), c.context.length];
}

/** Splay.algorithm.runFrom, specialised: final tree and total rotations. */
export function runSequence(t, xs) {
  let k = 0;
  for (const x of xs) { const [u, c] = run(t, x); t = u; k += c; }
  return [t, k];
}

// --- Updates (Splay/Updates/Algorithm/Abstract) ------------------------------

/** Updates.split: first k keys on the left. */
export function split(t, k) {
  if (k === 0) return { left: null, right: t, cost: 0 };
  const [u, c] = run(t, k - 1);
  if (u === null) return { left: null, right: null, cost: c };
  return { left: node(u[0], null), right: u[1], cost: c };
}

/** Updates.join: splay the maximum of the left tree, then hang the right tree. */
export function join(l, r) {
  if (l === null) return [r, 0];
  const [u, c] = run(l, size(l) - 1);
  if (u === null) return [r, c];
  return [node(u[0], r), c];
}

/** Updates.insert: a new key in gap k becomes the root. */
export function insert(t, k) {
  const s = split(t, k);
  return [node(s.left, s.right), s.cost];
}

/** Updates.delete */
export function remove(t, x) {
  const [u, c] = run(t, x);
  if (u === null) return [null, c];
  const [v, d] = join(u[0], u[1]);
  return [v, c + d];
}

// --- Static trees and sequence measures --------------------------------------

/** StaticTree.depth: edges on the search path to rank x. */
export function depth(t, x) {
  if (t === null) return 0;
  const [l, r] = t;
  if (x < size(l)) return depth(l, x) + 1;
  if (x === size(l)) return 0;
  return depth(r, x - size(l) - 1) + 1;
}

/** StaticTree.cost */
export const staticTreeCost = (t, xs) => xs.reduce((s, x) => s + depth(t, x) + 1, 0);

/** Nat.log2: floor of the binary logarithm, with log2 0 = 0. */
export const natLog2 = (n) => (n <= 1 ? 0 : Math.floor(Math.log2(n)));

/** workingSetNumber */
export function workingSetNumber(n, past, x) {
  if (!past.includes(x)) return n;
  const since = [];
  for (let i = past.length - 1; i >= 0 && past[i] !== x; i--) since.push(past[i]);
  return 1 + new Set(since).size;
}

/** workingSetSum */
export function workingSetSum(n, past, xs) {
  let total = 0;
  const seen = [...past];
  for (const x of xs) { total += 1 + natLog2(workingSetNumber(n, seen, x)); seen.push(x); }
  return total;
}

/** Real.logb 2 with Mathlib's junk value logb 2 0 = 0 (and |x| for x < 0). */
export const logb2 = (x) => (x === 0 ? 0 : Math.log2(Math.abs(x)));

/** Bounds.staticCost: frequency entropy plus one per request. */
export function staticCost(n, xs) {
  let s = xs.length;
  for (let x = 0; x < n; x++) {
    const q = xs.filter((y) => y === x).length;
    s += q * logb2(q === 0 ? 0 : xs.length / q);
  }
  return s;
}

/** Bounds.fingerCost */
export const fingerCost = (f, xs) => xs.reduce((s, x) => s + 1 + logb2(Math.abs(x - f) + 1), 0);

/** Splay.mass: total weight of a subtree whose keys start at lo. */
export function mass(w, t, lo = 0) {
  if (t === null) return 0;
  const [l, r] = t;
  return mass(w, l, lo) + w(lo + size(l)) + mass(w, r, lo + size(l) + 1);
}

/** Splay.potential: sum of log2 of all nonempty subtree masses. */
export function potential(w, t, lo = 0) {
  if (t === null) return 0;
  const [l, r] = t;
  return potential(w, l, lo) + potential(w, r, lo + size(l) + 1) + logb2(mass(w, t, lo));
}

// --- Rotations (Model/Abstract) ------------------------------------------------

/** Path from the root to rank x, as a list of 'L'/'R' moves, or null. */
export function pathTo(t, x, lo = 0) {
  const path = [];
  while (t !== null) {
    const k = lo + size(t[0]);
    if (x === k) return path;
    if (x < k) { path.push('L'); t = t[0]; } else { path.push('R'); lo = k + 1; t = t[1]; }
  }
  return null;
}

function rebuildAlong(t, path, f) {
  if (path.length === 0) return f(t);
  const [d, ...rest] = path;
  return d === 'L' ? node(rebuildAlong(t[0], rest, f), t[1]) : node(t[0], rebuildAlong(t[1], rest, f));
}

/**
 * Rotate rank x over its parent. Returns {tree, term} where `term` is the
 * derivation of `Rotate s t` built from the four constructors, or null if x
 * is the root.
 */
export function rotateUp(t, x) {
  const path = pathTo(t, x);
  if (!path || path.length === 0) return null;
  const toParent = path.slice(0, -1);
  const dir = path[path.length - 1];
  const tree = rebuildAlong(t, toParent, (p) => {
    if (dir === 'L') { const [[a, b], c] = p; return node(a, node(b, c)); } // Rotate.right
    const [a, [b, c]] = p; return node(node(a, b), c); // Rotate.left
  });
  let term = dir === 'L' ? '.right' : '.left';
  for (let i = toParent.length - 1; i >= 0; i--) term = `${toParent[i] === 'L' ? '.inLeft' : '.inRight'} ${term.includes(' ') ? `(${term})` : term}`;
  return { tree, term, constructor: dir === 'L' ? 'right' : 'left', depth: toParent.length };
}

/** Rank of the root, i.e. the x for which `Access s t x k` can hold. */
export const rootKey = (t) => (t === null ? null : size(t[0]));

/** Depth of every rank, and parent ranks, for drawing. */
export function layout(t) {
  const nodes = [];
  const walk = (s, lo, d, parent) => {
    if (s === null) return;
    const k = lo + size(s[0]);
    nodes.push({ key: k, depth: d, parent, subtreeLo: lo, subtreeSize: size(s), leftSize: size(s[0]) });
    walk(s[0], lo, d + 1, k);
    walk(s[1], k + 1, d + 1, k);
  };
  walk(t, 0, 0, null);
  return nodes.sort((a, b) => a.key - b.key);
}

export function height(t) {
  return t === null ? 0 : 1 + Math.max(height(t[0]), height(t[1]));
}

// --- Lean syntax for trees ------------------------------------------------------

export function toLean(t) {
  if (t === null) return '.nil';
  const arg = (s) => (s === null ? '.nil' : `(${toLean(s)})`);
  return `.node ${arg(t[0])} ${arg(t[1])}`;
}

export function fromLean(text) {
  const tokens = text.replace(/[()]/g, ' $& ').split(/\s+/).filter(Boolean);
  let i = 0;
  const parse = () => {
    const tok = tokens[i++];
    if (tok === '(') { const t = parse(); if (tokens[i++] !== ')') throw new Error('expected )'); return t; }
    const name = tok?.replace(/^(RotationBST\.)?(Tree)?\./, '');
    if (name === 'nil') return null;
    if (name === 'node') { const l = parse(); const r = parse(); return node(l, r); }
    throw new Error(`unexpected ${tok ?? 'end of input'}`);
  };
  const t = parse();
  if (i !== tokens.length) throw new Error('trailing input');
  return t;
}

// --- Generators -------------------------------------------------------------------

export function fromKeys(keys) {
  // Insert distinct keys into an unbalanced BST, then forget them.
  const ins = (ks) => {
    if (ks.length === 0) return null;
    const [k, ...rest] = ks;
    return node(ins(rest.filter((y) => y < k)), ins(rest.filter((y) => y > k)));
  };
  return ins(keys);
}

export function balanced(n) {
  if (n === 0) return null;
  const l = Math.floor((n - 1) / 2);
  return node(balanced(l), balanced(n - 1 - l));
}

export function leftPath(n) { let t = null; for (let i = 0; i < n; i++) t = node(t, null); return t; }
export function rightPath(n) { let t = null; for (let i = 0; i < n; i++) t = node(null, t); return t; }
export function zigzag(n) {
  let t = null;
  for (let i = 0; i < n; i++) t = i % 2 ? node(t, null) : node(null, t);
  return t;
}

export function rng(seed) {
  let s = seed >>> 0 || 1;
  return () => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s / 4294967296; };
}

export function randomTree(n, seed = 1) {
  const r = rng(seed);
  const keys = [...Array(n).keys()];
  for (let i = n - 1; i > 0; i--) { const j = Math.floor(r() * (i + 1)); [keys[i], keys[j]] = [keys[j], keys[i]]; }
  return fromKeys(keys);
}

export function makeTree(spec, n, seed) {
  switch (spec) {
    case 'balanced': return balanced(n);
    case 'left-path': return leftPath(n);
    case 'right-path': return rightPath(n);
    case 'zigzag': return zigzag(n);
    default: return randomTree(n, seed);
  }
}
