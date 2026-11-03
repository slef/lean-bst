// JavaScript transcription of the treap vocabulary of the offline construction
// (Structures/Treap/Abstract.lean, Models/Region/Abstract.lean,
// Models/Region/View/Abstract.lean). Trees are shapes as in tree.js; points are
// [key, time] arrays as in geometry.js. test/treap.test.mjs checks the
// invariants of the construction on GreedyASS point sets computed by Lean.

import { size } from './tree.js';

/** `nextTouch P time key`: first touch at or after `time`; Infinity is ⊤ (never again). */
export function nextTouch(P, time, key) {
  let best = Infinity;
  for (const [x, t] of P) if (x === key && t >= time && t < best) best = t;
  return best;
}

/** `lastTouch P key`: latest touch; -Infinity is ⊥ (never touched). */
export function lastTouch(P, key) {
  let best = -Infinity;
  for (const [x, t] of P) if (x === key && t > best) best = t;
  return best;
}

/** `Heap priority t lo`: every subtree root has minimum priority in its inorder interval. */
export function isHeap(priority, t, lo = 0) {
  if (t === null) return true;
  const [l, r] = t;
  const root = lo + size(l);
  for (let x = 0; x < size(t); x++) if (!(priority(root) <= priority(lo + x))) return false;
  return isHeap(priority, l, lo) && isHeap(priority, r, root + 1);
}

/** `HistoryHeap P t`: a max-heap of latest touches (Heap of the order dual). */
export const isHistoryHeap = (P, t) => isHeap((x) => -lastTouch(P, x), t, 0);

/**
 * The treap on ranks lo, …, lo + n − 1: the root is the key of minimum
 * priority. `Heap` imposes no tie-breaking rule; this function breaks ties
 * by the smaller key, which makes the treap unique.
 */
export function treap(n, priority, lo = 0) {
  if (n <= 0) return null;
  let best = lo;
  for (let x = lo + 1; x < lo + n; x++) if (priority(x) < priority(best)) best = x;
  return [treap(best - lo, priority, lo), treap(lo + n - best - 1, priority, best + 1)];
}

/** The next-touch treap used at the start of row `time`. */
export const nextTouchTreap = (n, P, time) => treap(n, (x) => nextTouch(P, time, x));

/**
 * `Region.project P time t lo`, flattened: the keys of the rooted region that
 * descends from the root while the visited key is touched on row `time`, and
 * the holes (untouched fringe subtrees) as [offset, subtree] pairs in inorder.
 */
export const project = (P, time, t, lo = 0) =>
  region(new Set(P.filter((p) => p[1] === time).map((p) => p[0])), t, lo);

/** The rooted region of `t` whose nodes are the keys in `touched`, stopping at other keys. */
export function region(touched, t, lo = 0) {
  const keys = [];
  const holes = [];
  const walk = (s, base) => {
    if (s === null) { holes.push([base, null]); return; }
    const root = base + size(s[0]);
    if (!touched.has(root)) { holes.push([base, s]); return; }
    walk(s[0], base);
    keys.push(root);
    walk(s[1], root + 1);
  };
  walk(t, lo);
  return { keys, holes };
}

/** `RowAdjacent P time a b`: no other point of row `time` lies between a and b (inclusive of b). */
export function rowAdjacent(P, time, a, b) {
  const lo = Math.min(a, b); const hi = Math.max(a, b);
  return P.every(([x, t]) => t !== time || x < lo || x > hi || x === a);
}

/** `keysAt P time`, sorted. */
export const keysAt = (P, time) => P.filter((p) => p[1] === time).map((p) => p[0]).sort((a, b) => a - b);

/** `pastPoints P time`. */
export const pastPoints = (P, time) => P.filter((p) => p[1] < time);

/**
 * Rearrange a region into heap order without touching its fringe, as in the
 * proof of `Region.heapify`: the active key of minimum priority (ties: the
 * smaller key) becomes the root, recursively; holes are plugged back in order.
 */
export function heapify(keys, holes, priority) {
  const build = (i, j) => { // keys[i..j), holes[i..j]
    if (i === j) return holes[i][1];
    let best = i;
    for (let k = i + 1; k < j; k++) if (priority(keys[k]) < priority(keys[best])) best = k;
    return [build(i, best), build(best + 1, j)];
  };
  return build(0, keys.length);
}

/**
 * The offline construction: T₀ is the next-touch treap for time 0, and T_{t+1}
 * rearranges the touched region of T_t (row t) into heap order for time t+1.
 * Returns the trees T₀, …, T_m and the regions, one per row.
 */
export function construction(n, P, m) {
  const trees = [nextTouchTreap(n, P, 0)];
  const regions = [];
  for (let time = 0; time < m; time++) {
    const r = project(P, time, trees[time]);
    regions.push(r);
    trees.push(heapify(r.keys, r.holes, (x) => nextTouch(P, time + 1, x)));
  }
  return { trees, regions };
}
