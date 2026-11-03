// JavaScript transcriptions of Wilber's interleave quantity
// (Bounds/Interleave/{Definitions,Transition,Wilber}/Abstract.lean) and of
// Tango's preference vocabulary (Algorithms/Tango/{Definitions,Preferences,
// Paths,Reference}/Abstract.lean). Trees are `null` (nil) or `[left, right]`,
// as in tree.js. test/interleave.test.mjs compares them with Lean.

import { size, height } from './tree.js';

export { height };

// --- Wilber.regions, leftRequests, rightRequests, alternations, interleave, switch

/** Region observations: `true` is the left region (the node and its left subtree). */
export const regions = (leftSize, sz, xs) => xs.filter((x) => x < sz).map((x) => x <= leftSize);
export const leftRequests = (leftSize, xs) => xs.filter((x) => x < leftSize);
export const rightRequests = (leftSize, xs) => xs.filter((x) => leftSize < x).map((x) => x - leftSize - 1);

export function alternations(bs) {
  let a = 0;
  for (let i = 0; i + 1 < bs.length; i++) if (bs[i] !== bs[i + 1]) a++;
  return a;
}

export function interleave(t, xs) {
  if (t === null) return 0;
  const [l, r] = t;
  const ls = size(l);
  return alternations(regions(ls, ls + 1 + size(r), xs))
    + interleave(l, leftRequests(ls, xs)) + interleave(r, rightRequests(ls, xs));
}

export const switchCost = (past, next) => (past.length === 0 ? 0 : past[past.length - 1] === next ? 0 : 1);

// --- Wilber.labels, absoluteInterleave

export const labels = (low, cut, high, xs) => xs.filter((x) => low <= x && x < high).map((x) => x <= cut);

export function absoluteInterleave(t, lo, xs) {
  if (t === null) return 0;
  const [l, r] = t;
  const ls = size(l);
  return alternations(labels(lo, lo + ls, lo + ls + 1 + size(r), xs))
    + absoluteInterleave(l, lo, xs) + absoluteInterleave(r, lo + ls + 1, xs);
}

// --- Wilber.topIn, transition, transitionKeys

export function topIn(t, lo, low, high) {
  if (t === null) return null;
  const k = lo + size(t[0]);
  if (k < low) return topIn(t[1], k + 1, low, high);
  if (high <= k) return topIn(t[0], lo, low, high);
  return k;
}

export function transition(t, low, cut, high) {
  const root = topIn(t, 0, low, high);
  if (root === null) return null;
  return root <= cut ? topIn(t, 0, cut + 1, high) : topIn(t, 0, low, cut + 1);
}

export function transitionKeys(reference, lo, actual) {
  if (reference === null) return [];
  const [l, r] = reference;
  const ls = size(l);
  const p = transition(actual, lo, lo + ls, lo + ls + 1 + size(r));
  return [...(p === null ? [] : [p]), ...transitionKeys(l, lo, actual), ...transitionKeys(r, lo + ls + 1, actual)];
}

// --- Tango.changes, changeCost, runs, initializations, preferenceChanges

export function changes(t, past, x) {
  if (t === null) return 0;
  const [l, r] = t;
  const ls = size(l);
  const sz = ls + 1 + size(r);
  if (!(x < sz)) return 0;
  const here = switchCost(regions(ls, sz, past), x <= ls);
  if (x < ls) return here + changes(l, leftRequests(ls, past), x);
  if (x === ls) return here;
  return here + changes(r, rightRequests(ls, past), x - ls - 1);
}

export function changeCost(t, past, xs) {
  let c = 0;
  let p = past.slice();
  for (const x of xs) { c += changes(t, p, x); p = [...p, x]; }
  return c;
}

export const runs = (trace) => (trace.length === 0 ? 0 : 1 + alternations(trace));

export function initializations(t, xs) {
  if (t === null) return 0;
  const [l, r] = t;
  const ls = size(l);
  return (regions(ls, ls + 1 + size(r), xs).length === 0 ? 0 : 1)
    + initializations(l, leftRequests(ls, xs)) + initializations(r, rightRequests(ls, xs));
}

export function preferenceChanges(t, xs) {
  if (t === null) return 0;
  const [l, r] = t;
  const ls = size(l);
  return runs(regions(ls, ls + 1 + size(r), xs))
    + preferenceChanges(l, leftRequests(ls, xs)) + preferenceChanges(r, rightRequests(ls, xs));
}

// --- Tango.decomposePaths, PathDecomposition.parts, preferredPaths

export const parts = ([first, rest]) => (first.length === 0 ? rest : [first, ...rest]);

export function decomposePaths(t, lo, past) {
  if (t === null) return [[], []];
  const [l, r] = t;
  const ls = size(l);
  const left = decomposePaths(l, lo, past);
  const right = decomposePaths(r, lo + ls + 1, past);
  const root = lo + ls;
  const obs = labels(lo, root, lo + ls + 1 + size(r), past);
  if (obs.length === 0) return [[root], [...parts(left), ...parts(right)]];
  if (obs[obs.length - 1]) return [[root, ...left[0]], [...left[1], ...parts(right)]];
  return [[root, ...right[0]], [...parts(left), ...right[1]]];
}

export const preferredPaths = (reference, past) => parts(decomposePaths(reference, 0, past));

// --- Tango.balanced

export function balanced(n) {
  if (n === 0) return null;
  return [balanced(Math.floor(n / 2)), balanced(Math.floor((n - 1) / 2))];
}

// --- Per-node bookkeeping for the figure

/** Every reference node with its absolute interval [lo, high) and its observed labels. */
export function nodeIntervals(t, xs, lo = 0, out = []) {
  if (t === null) return out;
  const [l, r] = t;
  const ls = size(l);
  const key = lo + ls;
  const high = key + 1 + size(r);
  out.push({ key, lo, high, labels: labels(lo, key, high, xs) });
  nodeIntervals(l, xs, lo, out);
  nodeIntervals(r, xs, key + 1, out);
  return out;
}

/** The reference search path for x: each node with its previous and next preferred side. */
export function searchPath(t, past, x, lo = 0, out = []) {
  if (t === null) return out;
  const [l, r] = t;
  const key = lo + size(l);
  const high = key + 1 + size(r);
  if (x < lo || x >= high) return out;
  const obs = labels(lo, key, high, past);
  out.push({ key, previous: obs.length ? obs[obs.length - 1] : null, next: x <= key });
  if (x < key) searchPath(l, past, x, lo, out);
  else if (x > key) searchPath(r, past, x, key + 1, out);
  return out;
}
