// Wilber's interleave quantity and Tango's preference bookkeeping, as used by
// the `reference` figure, against values computed by Lean (vectors.reference).

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as W from '../src/assets/viz/interleave.js';

const here = dirname(fileURLToPath(import.meta.url));
const vectorsPath = join(here, '..', 'build', 'vectors.json');
const vectors = existsSync(vectorsPath) ? JSON.parse(readFileSync(vectorsPath, 'utf8')) : null;
const skip = vectors?.reference ? false : 'run `npm run extract` first';

test('interleave, changes, preferences and preferred paths agree with Lean', { skip }, () => {
  const cases = vectors.reference.filter((v) => v.requests);
  assert.ok(cases.length >= 10);
  for (const v of cases) {
    const { tree: t, requests: xs } = v;
    const tag = JSON.stringify(xs);
    assert.equal(W.interleave(t, xs), v.interleave, `interleave ${tag}`);
    assert.equal(W.absoluteInterleave(t, 0, xs), v.absoluteInterleave, `absoluteInterleave ${tag}`);
    assert.deepEqual(xs.map((x, j) => W.changes(t, xs.slice(0, j), x)), v.changes, `changes ${tag}`);
    assert.equal(W.changeCost(t, [], xs), v.interleave, `changeCost = interleave ${tag}`);
    assert.equal(W.preferenceChanges(t, xs), v.preferenceChanges);
    assert.equal(W.initializations(t, xs), v.initializations);
    const paths = [];
    for (let j = 0; j <= xs.length; j++) paths.push(W.preferredPaths(t, xs.slice(0, j)));
    assert.deepEqual(paths, v.preferredPaths, `preferredPaths ${tag}`);
    assert.deepEqual(W.transitionKeys(t, 0, t), v.transitionKeys);
    assert.equal(W.height(t), v.height);
  }
});

test('Tango.balanced agrees with Lean', { skip }, () => {
  const cases = vectors.reference.filter((v) => v.balanced !== undefined);
  assert.ok(cases.length >= 10);
  for (const v of cases) assert.deepEqual(W.balanced(v.balanced), v.tree);
});

test('per-node labels sum to the interleave quantity; search paths count changes', () => {
  for (let n = 1; n <= 12; n++) {
    const t = W.balanced(n);
    const xs = Array.from({ length: 3 * n }, (_, i) => (i * 7 + 3) % n);
    const total = W.nodeIntervals(t, xs).reduce((s, v) => s + W.alternations(v.labels), 0);
    assert.equal(total, W.interleave(t, xs));
    xs.forEach((x, j) => {
      const path = W.searchPath(t, xs.slice(0, j), x);
      const switches = path.filter((p) => p.previous !== null && p.previous !== p.next).length;
      assert.equal(switches, W.changes(t, xs.slice(0, j), x));
    });
  }
});
