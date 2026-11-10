# Book updates needed after the classical cleanup

The classical formalizations (ROADMAP entries 1, 3–9) were cleaned up on
branch `classical-cleanup` before merging. This file lists what a chapter,
`@decl`/`@stmt` line or `[[…]]` reference may need. Delete it once the book
follows.

## References in `book/src` that break

These cite declarations that are now `export` aliases. An alias is not a
declaration, so the extractor will not find it; point each one at the `Tree.`
name. The Lean code still accepts `Tango.height`, `Tango.balanced`.

| File:line | Reference | Replace with |
| --- | --- | --- |
| `chapters/algorithms/preferred-paths.md:31` | `@decl RotationBST.Tango.height` | `@decl RotationBST.Tree.height` |
| `chapters/algorithms/preferred-paths.md:41` | `@decl RotationBST.Tango.balanced` | `@decl RotationBST.Tree.balanced` |
| `chapters/algorithms/tango-linear.md:138` | `[[RotationBST.Tango.height]]` | `[[RotationBST.Tree.height]]` |
| `chapters/algorithms/tango.md:196` | `[[RotationBST.Tango.balanced]]` | `[[RotationBST.Tree.balanced]]` |
| `chapters/algorithms/combined-finger.md:69, 180` | `[[Tango.balanced]]` | `[[Tree.balanced]]` |
| `chapters/classical/static-trees.md:9` | `[[Tango.balanced]]` | `[[Tree.balanced]]` (it is now the classical balanced tree too) |
| `assets/viz/interleave.js:128` | comment `Tango.balanced` | `Tree.balanced` (comment only) |

Text that is now out of date:

- `chapters/bounds/bounds.md:124` says "there is no `Has…Bound` property for
  this benchmark" (dynamic finger). `HasDynamicFingerBound` now exists
  (`Bounds/DynamicFinger/Definitions/Abstract.lean`), with
  `Bounds.dynamicFinger_implies_staticFinger`.
- `chapters/algorithms/tango-linear.md` composes the bottom-up policy and the
  reset by hand; `Tango.Algorithm.Results.exists_competitive_linear` now
  states the result.

## Moved definitions (old name → new name)

| Old | New | Note |
| --- | --- | --- |
| `Tango.height` (def) | `Tree.height` | In `Models/Rotation/Abstract.lean`, next to `Tree.size` and `Tree.depth`. Same equations (`1 + max …`). `Tango.height` is an alias. |
| `Tango.balanced` (def) | `Tree.balanced` | Same file. `Tango.balanced` is an alias. In Lean, `balanced.eq_def` must now be written `Tree.balanced.eq_def` (the alias does not provide it). |
| `Tango.balanced_size`, `Tango.balanced_height_of_lt_pow`, `Tango.balanced_height` | `Tree.balanced_size`, `Tree.balanced_height_of_lt_pow`, `Tree.balanced_height` | In `Models/Rotation/Shapes.lean`; Tango aliases kept. `Tango.Reference.Results.balanced_reference` is unchanged. |
| `Classical.Static.balanced`, `Classical.Static.height` | `Tree.balanced`, `Tree.height` | The classical copies are gone. The classical height was `max + 1`, the shared one is `1 + max` (same values). |
| `Classical/Static/Definitions/Abstract.lean` (file) | deleted | Its two definitions are in `Models/Rotation/Abstract.lean`. |
| `Classical.Static.Optimal.treeCost` | `LazyFinger.intervalCost` | Identical definition, in `Bounds/LazyFinger/Edges/Definitions/Abstract.lean`. |
| `Classical.Static.Optimal.Monotone` | `Classical.Static.Optimal.InclusionMonotone` | Avoids shadowing Mathlib's `Monotone`. Hypotheses of Yao's and Knuth's results now read `InclusionMonotone W`. |
| `Classical.Scapegoat.insertLeaf t k` | `Tree.insertAt t k` | In `Models/Dictionary/Definitions/Abstract.lean`. |
| `Classical.RankBalanced.leafAt t g` | `LabelledTree.insertAt t g 0` | Same file; it takes the new node's datum (rank `0`) as an argument. |
| `Classical.Random.insertAll` | `Classical.Random.insertKeys` | Avoids two different `insertAll`s (`RankBalanced.insertAll` is unchanged). |
| `Dictionary.depth_left`, `depth_root`, `depth_right` | `Tree.depth_left`, `Tree.depth_root`, `Tree.depth_right` | `Models/Rotation/Shapes.lean`. |
| `Dictionary.depth_le_rotate`, `Dictionary.depth_le_rotations` | `Rotate.depth_le_reverse`, `Rotations.depth_le_reverse` | `Models/Rotation/Shapes.lean`, with forward versions `Rotate.depth_le`, `Rotations.depth_le`. `StaticTree.Trace.rotate_depth`, `rotations_depth` keep their names and statements; they are now one-line consequences. |
| `Classical.Scapegoat.insertLeaf_depth_lt/_ge/_other`, `insertLeaf_parent`, `splice_depth` | `Dictionary.insertAt_depth_lt/_ge/_other`, `Dictionary.insertAt_parent`, `Dictionary.splice_depth` | New file `Models/Dictionary/Depth.lean`. |
| `Scapegoat.insertLeaf_size`, `insertLeaf_splice`, `RankBalanced.leafAt_size`, `leafAt_splice` | `Dictionary.insertAt_size`, `unit_insertAt_splice`, `insertAt_erase_size`, `insertAt_splice` | `Models/Dictionary/Basic.lean`. |
| `Scapegoat.rebuild_size` | `WeightBalanced.rebuild_size` | Proof files only. |
| `Bounds.logb_nat_nonneg` | same name | Moved from `Implications/Entropy.lean` to `Implications/LogSum.lean`. |
| `RankBalanced.le_logb_of_pow`, `Classical.Static.log2_le_logb` | `Bounds.le_logb_of_pow` | `Implications/LogSum.lean`. Proof files only. |
| `Bounds.logb_dist_finger_nonneg` | removed | Use `Bounds.logb_nat_nonneg`. |

## Renamed or changed statements on reading surfaces

| Old | New | Note |
| --- | --- | --- |
| `Classical.Static.Results.balanced_height` | `…balanced_height_eq` | The equality `height (balanced n) = ⌊log₂ n⌋ + 1` for `n > 0`. `Tree.balanced_height` is now the `≤` bound for all `n`. |
| `Classical.Static.Results.log2_lt_height` | `…log2_add_one_le_height` | The statement is `⌊log₂ n⌋ + 1 ≤ height t`. |
| `Classical.Static.Results.balanced_size` | unchanged | Now a delegation to `Tree.balanced_size`. Still 8 root declarations. |
| `Optimal.Results.cost_le_treeCost` | `Optimal.Results.cost_le_intervalCost` | |
| `Static.Optimal.Results.weightedCost_eq_treeCost` | `…weightedCost_eq_intervalCost` | |
| `Optimal.Results.tree_cost`, `cost_le_intervalCost`, `weightedCost_eq_intervalCost` | | Statements now use `LazyFinger.intervalCost`. |
| `Optimal.Results` Yao/Knuth statements | | Hypothesis `Monotone W` became `InclusionMonotone W`. |
| `Classical.Random.Results.insertAll_treap` | `…insertKeys_treap` | `random_bst_depth` and `random_bst_depth_le` keep their names; their statements use `insertKeys`. |
| `Classical.RankBalanced.Results.insert_step` | unchanged name | The search charge is now `(t.insertAt g 0).erase.depth g` instead of `(leafAt t g).erase.depth g`. |
| `Dictionary.Results.depth_rotations` | `Dictionary.Results.rotations_depth_reverse` | Matches `StaticTree.Trace.Results.rotations_depth` (the other direction). |
| `Classical.Scapegoat.Results` | | Helper `one_lt_inv` renamed `one_lt_inv_alpha` (not on the reading surface). |

## Unchanged, for reference

`RankBalanced.insert` keeps its name, like `Splay.Updates.insert`; tests write
it in full because of Lean's `insert` notation. `RankBalanced.insertAll`,
`insertEdits` and all other `Results` names are unchanged.
