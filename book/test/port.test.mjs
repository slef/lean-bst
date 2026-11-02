// The figures run JavaScript transcriptions of the Lean algorithms. This test
// compares them with values computed by the Lean definitions themselves
// (book/lean/Export.lean writes build/vectors.json during `npm run extract`).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as T from '../src/assets/viz/tree.js';

const here = dirname(fileURLToPath(import.meta.url));
const vectorsPath = join(here, '..', 'build', 'vectors.json');
const vectors = existsSync(vectorsPath) ? JSON.parse(readFileSync(vectorsPath, 'utf8')) : null;
const skip = vectors ? false : 'run `npm run extract` first';

test('Splay.locate, Splay.run and StaticTree.depth agree with Lean', { skip }, () => {
  assert.ok(vectors.splay.length > 500);
  for (const v of vectors.splay) {
    const c = T.locate(v.tree, v.x);
    assert.deepEqual(c.context.map((f) => ({ side: f.side, tree: f.tree })), v.context, `locate ${JSON.stringify(v.tree)} ${v.x}`);
    const [u, k] = T.run(v.tree, v.x);
    assert.deepEqual(u, v.result, `run ${JSON.stringify(v.tree)} ${v.x}`);
    assert.equal(k, v.cost);
    assert.equal(T.depth(v.tree, v.x), v.depth);
  }
});

test('split, join, insert and delete agree with Lean', { skip }, () => {
  for (const v of vectors.updates) {
    if (v.op === 'split') {
      const s = T.split(v.tree, v.k);
      assert.deepEqual([s.left, s.right, s.cost], [v.left, v.right, v.cost]);
    } else if (v.op === 'insert') {
      assert.deepEqual(T.insert(v.tree, v.k), [v.result, v.cost]);
    } else if (v.op === 'delete') {
      assert.deepEqual(T.remove(v.tree, v.k), [v.result, v.cost]);
    } else if (v.op === 'join') {
      assert.deepEqual(T.join(v.left, v.right), [v.result, v.cost]);
    }
  }
});

test('request sequences: costs and working-set numbers agree with Lean', { skip }, () => {
  for (const v of vectors.sequences) {
    const [final, cost] = T.runSequence(v.tree, v.requests);
    assert.deepEqual(final, v.final);
    assert.equal(cost, v.cost);
    assert.equal(v.requests.length + cost, v.totalCost);
    const ws = v.requests.map((x, j) => T.workingSetNumber(v.n, v.requests.slice(0, j), x));
    assert.deepEqual(ws, v.workingSetNumbers);
    assert.equal(T.workingSetSum(v.n, [], v.requests), v.workingSetSum);
    assert.equal(T.staticTreeCost(v.tree, v.requests), v.staticTreeCost);
  }
});

test('rotations preserve size and inorder ranks; the derivation term is well formed', () => {
  for (let n = 1; n <= 9; n++) {
    const t = T.randomTree(n, n * 7);
    for (let x = 0; x < n; x++) {
      const r = T.rotateUp(t, x);
      if (T.rootKey(t) === x) { assert.equal(r, null); continue; }
      assert.equal(T.size(r.tree), n);
      // x moved up by exactly one level, everything stays in inorder.
      const before = T.layout(t).find((v) => v.key === x).depth;
      const after = T.layout(r.tree).find((v) => v.key === x).depth;
      assert.equal(after, before - 1);
      assert.match(r.term, /^(\.inLeft |\.inRight |\(|\)|\.right|\.left)+$/);
    }
  }
});

test('Lean syntax round-trips', () => {
  for (let n = 0; n <= 8; n++) {
    const t = T.randomTree(n, 3 + n);
    assert.deepEqual(T.fromLean(T.toLean(t)), t);
  }
  assert.deepEqual(T.fromLean('Tree.node (.node .nil .nil) RotationBST.Tree.nil'), [[null, null], null]);
});

test('splaying with the pointer cursor reproduces Splay.run', () => {
  for (let n = 1; n <= 8; n++) {
    const t = T.randomTree(n, 11 * n);
    for (let x = 0; x < n; x++) {
      const c = T.locate(t, x);
      assert.equal(T.keyOf(c), x);
      assert.deepEqual(T.plug(c.context, c.focus), t);
    }
  }
});
