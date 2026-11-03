// JavaScript transcription of Structures/SplitTree: unlabelled 2–3–4 trees
// (`Geometric.Split.Multiway`), their binary representation, the minimum
// finger and its comparison-tree view, and the split accounting charge.
// A multiway tree is null (`nil`) or an array of 2, 3 or 4 children; binary
// trees are null or [left, right], as in tree.js. Checked against Lean by
// test/multiway.test.mjs.

import { natLog2, node } from './tree.js';

/** Multiway.size: keys, one fewer than the children at each node. */
export function size(t) {
  if (t === null) return 0;
  return t.reduce((s, c) => s + size(c), 0) + t.length - 1;
}

/** Multiway.nodes */
export function nodes(t) {
  if (t === null) return 0;
  return t.reduce((s, c) => s + nodes(c), 0) + 1;
}

/** Multiway.binary */
export function binary(t) {
  if (t === null) return null;
  const b = t.map(binary);
  switch (t.length) {
    case 2: return node(b[0], b[1]);
    case 3: return node(b[0], node(b[1], b[2]));
    default: return node(node(b[0], b[1]), node(b[2], b[3]));
  }
}

/** Height h with `Balanced h t`, or -1 if the leaves are at different depths. */
export function balancedHeight(t) {
  if (t === null) return 0;
  const hs = t.map(balancedHeight);
  return hs.every((h) => h >= 0 && h === hs[0]) ? hs[0] + 1 : -1;
}

const is = (t, k) => t !== null && t.length === k;

/** Multiway.prepareLeft */
export function prepareLeft(t) {
  if (is(t, 2) && is(t[0], 2)) {
    const [[a, b], s] = t;
    if (is(s, 2)) return [[a, b, s[0], s[1]], 0];
    if (is(s, 3)) { const [c, d, e] = s; return [[[a, b, c], [d, e]], 2]; }
    if (is(s, 4)) { const [c, d, e, f] = s; return [[[a, b, c], [d, e, f]], 3]; }
  }
  return [t, 0];
}

/** Multiway.prepareRight */
export function prepareRight(t) {
  if (is(t, 2) && is(t[1], 2)) {
    const [s, [x, y]] = t;
    if (is(s, 2)) return [[s[0], s[1], x, y], 0];
    if (is(s, 3)) { const [a, b, c] = s; return [[[a, b], [c, x, y]], 2]; }
    if (is(s, 4)) { const [a, b, c, d] = s; return [[[a, b, c], [d, x, y]], 4]; }
  }
  return [t, 0];
}

// --- Contexts (Multiway/Context) ---------------------------------------------
// A frame is { pos, siblings }: the ancestor's children with the focus omitted
// at index pos (twoLeft = pos 0 of 2, …, fourLast = pos 3 of 4).

/** Context.Frame.fill */
export const fill = (f, t) => [...f.siblings.slice(0, f.pos), t, ...f.siblings.slice(f.pos)];

/** Context.plug: nearest ancestor first. */
export const plug = (fs, t) => fs.reduce((u, f) => fill(f, u), t);

// --- The minimum finger (Finger) ---------------------------------------------

/** Finger.leftSpine: ancestors of the leftmost leaf, nearest first. */
export function leftSpine(t) {
  if (t === null) return [];
  return [...leftSpine(t[0]), { pos: 0, siblings: t.slice(1) }];
}

/** Finger.ascend */
export function ascend(fs, focus, rank) {
  let levels = 0;
  for (const f of fs) {
    if (rank < size(focus)) return levels;
    levels++;
    focus = fill(f, focus);
  }
  return levels;
}

/** Finger.searchLevels */
export const searchLevels = (t, rank) => ascend(leftSpine(t), null, rank);

/** Finger.mirror */
export const mirror = (t) => (t === null ? null : t.map(mirror).reverse());

const natSub = (a, b) => Math.max(0, a - b);

/** Finger.nearSearchLevels */
export function nearSearchLevels(t, rank) {
  const other = natSub(natSub(size(t), 1), rank);
  return rank <= other ? searchLevels(t, rank) : searchLevels(mirror(t), other);
}

/** Finger.comb: a right spine with the listed subtrees hanging on the left. */
export const comb = (spine, tail) => spine.reduceRight((acc, a) => node(a, acc), tail);

/** Finger.binaryView */
export function binaryView(t) {
  if (t === null) return { spine: [], tail: null };
  const v = binaryView(t[0]);
  const rest = t.slice(1).map(binary);
  return { spine: [...v.spine, v.tail, ...rest.slice(0, -1)], tail: rest[rest.length - 1] };
}

/** Finger.BinaryView.tree */
export const viewTree = (v) => comb(v.spine, v.tail);

/** Finger.viewCost */
export function viewCost(t) {
  if (t === null) return 0;
  const len = binaryView(t[0]).spine.length;
  return viewCost(t[0]) + (t.length === 4 ? 2 * len + 1 : len);
}

// --- Accounting ----------------------------------------------------------------

/** Split.charge */
export const charge = (left, right) => 1 + natLog2(Math.min(left, right) + 1);

/** Split.totalCharge, for a binary split hierarchy. */
export function totalCharge(t) {
  if (t === null) return 0;
  const [l, r] = t;
  const sl = l === null ? 0 : sizeBin(l);
  const sr = r === null ? 0 : sizeBin(r);
  return totalCharge(l) + totalCharge(r) + charge(sl, sr);
}
const sizeBin = (t) => (t === null ? 0 : sizeBin(t[0]) + 1 + sizeBin(t[1]));

// --- Drawing helpers -------------------------------------------------------------

/** Multiway nodes with their key ranks and depth, for drawing. */
export function layoutMultiway(t) {
  const out = [];
  const walk = (s, lo, d, parent) => {
    if (s === null) return;
    const keys = [];
    const childLo = [];
    let at = lo;
    s.forEach((c, i) => {
      childLo.push(at);
      at += size(c);
      if (i < s.length - 1) { keys.push(at); at++; }
    });
    const id = out.length;
    out.push({ id, keys, depth: d, parent });
    s.forEach((c, i) => walk(c, childLo[i], d + 1, id));
  };
  walk(t, 0, 0, null);
  return out;
}

/** A pseudo-random balanced 2–3–4 tree of height h. */
export function randomMultiway(h, r) {
  if (h === 0) return null;
  const k = 2 + Math.floor(r() * 3);
  return Array.from({ length: k }, () => randomMultiway(h - 1, r));
}
