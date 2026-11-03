// JavaScript transcription of the geometric model (Models/Geometric/*/Abstract.lean)
// and of the GreedyASS sweep (Algorithms/GreedyASS/Algorithm/Abstract.lean).
// A point is an array [key, time]; a point set is an array of distinct points.
// test/geometry.test.mjs compares these functions with values computed by Lean.

export const pointKey = (p) => `${p[0]},${p[1]}`;
export const samePoint = (p, q) => p[0] === q[0] && p[1] === q[1];

/** Sort by time, then key (the order of the Lean test vectors). */
export const sortPoints = (P) => P.slice().sort((a, b) => a[1] - b[1] || a[0] - b[0]);

/** Union of point sets, without duplicates. */
export function union(P, Q) {
  const seen = new Set(P.map(pointKey));
  const out = P.slice();
  for (const q of Q) if (!seen.has(pointKey(q))) { seen.add(pointKey(q)); out.push(q); }
  return out;
}

export const has = (P, p) => P.some((q) => samePoint(p, q));

/** `Rectangle a b p`: p lies in the closed axis-aligned rectangle spanned by a and b. */
export function rectangle(a, b, p) {
  return Math.min(a[0], b[0]) <= p[0] && p[0] <= Math.max(a[0], b[0])
    && Math.min(a[1], b[1]) <= p[1] && p[1] <= Math.max(a[1], b[1]);
}

/** The rectangle of a and b is satisfied: degenerate, or it contains a third point of P. */
export function satisfiedPair(P, a, b) {
  if (a[0] === b[0] || a[1] === b[1]) return true;
  return P.some((p) => !samePoint(p, a) && !samePoint(p, b) && rectangle(a, b, p));
}

/** `ASS P`, with a witness pair whose rectangle is empty when it fails. */
export function checkASS(P) {
  for (const a of P) {
    for (const b of P) {
      if (!satisfiedPair(P, a, b)) return { ok: false, witness: [a, b] };
    }
  }
  return { ok: true, witness: null };
}
export const isASS = (P) => checkASS(P).ok;

/** `row time keys`. */
export const row = (time, keys) => keys.map((x) => [x, time]);

/** `Visible P time request q`: q is an old point whose rectangle with the request has no third old point. */
export function visible(P, time, request, q) {
  if (q[0] === request) return false;
  const r = [request, time];
  return P.every((p) => samePoint(p, q) || !rectangle(q, r, p));
}

/** `greedySweep time request P`: the request plus the keys of all visible old points, sorted. */
export function greedySweep(time, request, P) {
  const keys = new Set([request]);
  for (const q of P) if (visible(P, time, request, q)) keys.add(q[0]);
  return [...keys].sort((a, b) => a - b);
}

/** `fill step time P xs`, returning the final point set. */
export function fill(xs, step = greedySweep, time = 0, P = []) {
  let points = P;
  xs.forEach((x, j) => { points = union(points, row(time + j, step(time + j, x, points))); });
  return points;
}

/** The rows added by `fill`, one array of keys per request. */
export function rows(xs, step = greedySweep, time = 0, P = []) {
  let points = P;
  return xs.map((x, j) => {
    const keys = step(time + j, x, points);
    points = union(points, row(time + j, keys));
    return keys;
  });
}

/** `rowCost step time P xs`: one unit per point added, including each request. */
export const rowCost = (xs, step = greedySweep, time = 0, P = []) =>
  rows(xs, step, time, P).reduce((s, keys) => s + keys.length, 0);

/** `requestsAt time xs`. */
export const requestsAt = (time, xs) => xs.map((x, j) => [x, time + j]);

/** `Completion n time request P keys`. */
export function completion(n, time, request, P, keys) {
  return keys.includes(request) && keys.every((x) => x >= 0 && x < n)
    && isASS(union(P, row(time, keys)));
}

/** The exhaustive minimum-row rule `greedy n time request P` (exponential; small n only). */
export function greedy(n, time, request, P) {
  let best = [...Array(n).keys()];
  for (let mask = 0; mask < 1 << n; mask++) {
    const keys = [];
    for (let x = 0; x < n; x++) if (mask >> x & 1) keys.push(x);
    if (completion(n, time, request, P, keys) && keys.length < best.length) best = keys;
  }
  return best;
}
