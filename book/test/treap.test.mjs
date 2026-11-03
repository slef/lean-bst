// The offline construction of Structures/Treap on GreedyASS point sets
// computed by Lean (build/vectors.json, "geometric"): at each row the touched
// keys are exactly the top region of the next-touch treap, rearranging that
// region alone yields the next treap, and the tree is simultaneously a
// max-heap of latest touches.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as R from '../src/assets/viz/treap-lib.js';
import { size } from '../src/assets/viz/tree.js';

const here = dirname(fileURLToPath(import.meta.url));
const vectorsPath = join(here, '..', 'build', 'vectors.json');
const vectors = existsSync(vectorsPath) ? JSON.parse(readFileSync(vectorsPath, 'utf8')) : null;
const skip = vectors?.geometric ? false : 'run `npm run extract` first';

test('next-touch treaps realize GreedyASS point sets row by row', { skip }, () => {
  assert.ok(vectors.geometric.length >= 10);
  for (const v of vectors.geometric) {
    const { n, points: P, requests: xs } = v;
    const m = xs.length;
    const { trees } = R.construction(n, P, m);
    let cost = 0;
    for (let time = 0; time < m; time++) {
      const t = trees[time];
      const u = trees[time + 1];
      const where = `n=${n} xs=${xs} time=${time}`;
      assert.equal(size(t), n);
      assert.ok(R.isHeap((x) => R.nextTouch(P, time, x), t), `heap ${where}`);
      assert.ok(R.isHeap((x) => R.nextTouch(P, time + 1, x), u), `restored heap ${where}`);
      assert.ok(R.isHistoryHeap(R.pastPoints(P, time), t), `history heap ${where}`);
      // Region.project selects exactly the row: keysAt P time.
      const before = R.project(P, time, t);
      assert.deepEqual(before.keys, R.keysAt(P, time), `project ${where}`);
      assert.ok(before.keys.includes(xs[time]), `visits ${where}`);
      // The next treap differs only inside that region (Region.Same).
      const after = R.region(new Set(before.keys), u);
      assert.deepEqual(after.keys, before.keys, `same keys ${where}`);
      assert.deepEqual(after.holes, before.holes, `same fringe ${where}`);
      // The geometric lemma behind RowAdjacent.
      for (const a of before.keys) {
        for (let b = 0; b < n; b++) {
          if (a !== b && R.rowAdjacent(P, time, a, b)) {
            assert.ok(R.nextTouch(P, time + 1, a) <= R.nextTouch(P, time + 1, b), `adjacent ${where} ${a} ${b}`);
          }
        }
      }
      cost += before.keys.length;
    }
    assert.equal(cost, P.length);
    assert.equal(cost, v.rowCost);
  }
});

test('heap and treap helpers', () => {
  const pr = [3, 1, 4, 1, 5];
  const t = R.treap(5, (x) => pr[x]);
  assert.ok(R.isHeap((x) => pr[x], t));
  assert.equal(size(t[0]), 1); // root is rank 1, the first minimum
  assert.equal(R.nextTouch([[2, 3], [2, 7]], 4, 2), 7);
  assert.equal(R.nextTouch([[2, 3]], 4, 2), Infinity);
  assert.equal(R.lastTouch([], 0), -Infinity);
  assert.ok(R.rowAdjacent([[1, 0], [4, 0]], 0, 1, 3));
  assert.ok(!R.rowAdjacent([[1, 0], [2, 0]], 0, 1, 3));
});
