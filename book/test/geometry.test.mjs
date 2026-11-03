// The geometric figures run src/assets/viz/geometry.js, a transcription of the
// geometric model and of GreedyASS. Compare it with values computed by Lean.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as G from '../src/assets/viz/geometry.js';

const here = dirname(fileURLToPath(import.meta.url));
const vectorsPath = join(here, '..', 'build', 'vectors.json');
const vectors = existsSync(vectorsPath) ? JSON.parse(readFileSync(vectorsPath, 'utf8')) : null;
const skip = vectors ? false : 'run `npm run extract` first';

test('GreedyASS point sets and row costs agree with Lean', { skip }, () => {
  assert.ok(vectors.geometric.length >= 10);
  for (const v of vectors.geometric) {
    const P = G.fill(v.requests);
    assert.deepEqual(G.sortPoints(P), v.points, `fill ${JSON.stringify(v.requests)}`);
    assert.equal(G.rowCost(v.requests), v.rowCost);
    assert.equal(G.isASS(P), v.satisfied);
    for (const r of G.requestsAt(0, v.requests)) assert.ok(G.has(P, r));
  }
});

test('arboral satisfaction agrees with Lean', { skip }, () => {
  let yes = 0;
  for (const v of vectors.ass) {
    const c = G.checkASS(v.points);
    assert.equal(c.ok, v.satisfied, JSON.stringify(v.points));
    if (!c.ok) {
      const [a, b] = c.witness;
      assert.ok(a[0] !== b[0] && a[1] !== b[1]);
      assert.ok(!v.points.some((p) => !G.samePoint(p, a) && !G.samePoint(p, b) && G.rectangle(a, b, p)));
    } else yes++;
  }
  assert.ok(yes > 0 && yes < vectors.ass.length);
});

test('the sweep is the minimum completion of each row (small cases)', () => {
  for (let n = 1; n <= 5; n++) {
    for (let seed = 1; seed <= 6; seed++) {
      const xs = Array.from({ length: 6 }, (_, j) => (seed * 7 + j * (seed + 3) * 5) % n);
      let P = [];
      xs.forEach((x, time) => {
        const sweep = G.greedySweep(time, x, P);
        assert.deepEqual(G.greedy(n, time, x, P), sweep);
        assert.ok(G.completion(n, time, x, P, sweep));
        P = G.union(P, G.row(time, sweep));
      });
    }
  }
});
