// The split-tree figure runs src/assets/viz/multiway.js. This test compares it
// with values computed by the Lean definitions in Structures/SplitTree
// (book/lean/Export.lean writes build/vectors.json during `npm run extract`).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as M from '../src/assets/viz/multiway.js';
import * as T from '../src/assets/viz/tree.js';

const here = dirname(fileURLToPath(import.meta.url));
const vectorsPath = join(here, '..', 'build', 'vectors.json');
const vectors = existsSync(vectorsPath) ? JSON.parse(readFileSync(vectorsPath, 'utf8')) : null;
const skip = vectors?.multiway ? false : 'run `npm run extract` first';

test('2–3–4 trees: size, binary, finger view and search levels agree with Lean', { skip }, () => {
  const trees = vectors.multiway.filter((v) => 'tree' in v);
  assert.ok(trees.length >= 20);
  for (const v of trees) {
    const t = v.tree;
    const where = JSON.stringify(t);
    assert.ok(M.balancedHeight(t) > 0, where);
    assert.equal(M.size(t), v.size, where);
    assert.deepEqual(M.binary(t), v.binary, where);
    const view = M.binaryView(t);
    assert.deepEqual(M.viewTree(view), v.view, where);
    assert.equal(view.spine.length, v.spine, where);
    assert.equal(M.viewCost(t), v.viewCost, where);
    assert.deepEqual([...Array(v.size).keys()].map((r) => M.searchLevels(t, r)), v.searchLevels, where);
    assert.deepEqual([...Array(v.size).keys()].map((r) => M.nearSearchLevels(t, r)), v.nearSearchLevels, where);
    assert.deepEqual(M.prepareLeft(t), v.prepareLeft, where);
    assert.deepEqual(M.prepareRight(t), v.prepareRight, where);
    assert.deepEqual(M.mirror(t), v.mirror, where);
    // The theorems of Geometric.Split.Results, checked on the same inputs.
    const h = M.balancedHeight(t);
    assert.ok(M.viewCost(t) <= 3 * M.size(t));
    assert.ok(view.spine.length <= 3 * h);
    assert.deepEqual(M.plug(M.leftSpine(t), null), t);
    assert.equal(M.leftSpine(t).length, h);
    for (let r = 0; r < v.size; r++) {
      assert.ok(T.depth(v.view, r) <= 5 * T.natLog2(r + 1) + 6);
      assert.ok(M.nearSearchLevels(t, r) <= T.natLog2(Math.min(r, v.size - 1 - r) + 1) + 1);
    }
    assert.equal(T.rootKey(v.view), 0);
  }
});

test('the split accounting charge agrees with Lean', { skip }, () => {
  const hierarchies = vectors.multiway.filter((v) => 'totalChargeTree' in v);
  assert.ok(hierarchies.length > 0);
  for (const v of hierarchies) {
    assert.equal(M.totalCharge(v.totalChargeTree), v.totalCharge);
    assert.ok(v.totalCharge <= 2 * T.size(v.totalChargeTree));
  }
});

test('prepareLeft and prepareRight keep every key', () => {
  const r = T.rng(7);
  for (let i = 0; i < 200; i++) {
    const t = M.randomMultiway(2 + (i % 3), r);
    for (const prep of [M.prepareLeft, M.prepareRight]) {
      const [u] = prep(t);
      assert.equal(M.size(u), M.size(t));
      assert.equal(T.size(M.binary(u)), T.size(M.binary(t)));
    }
  }
});
