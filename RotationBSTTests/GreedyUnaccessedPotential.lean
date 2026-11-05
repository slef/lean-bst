module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyUnaccessedPotential
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def points (xs : List Nat) : Finset Point := fill greedySweep 0 ∅ xs
private def next (xs : List Nat) (searched : Nat) : Finset Point :=
  points xs ∪ row xs.length (greedySweep xs.length searched (points xs))

-- A repeated search inserts a new external column between the two old
-- corners. Both old corners are untouched and cease to be top corners.
-- Their opposite external queries stay undefined.
example : greedySweep 3 1 (points [0, 2, 1]) = {1} ∧
    External (points [0, 2, 1]) (0, 2) ∧ External (points [0, 2, 1]) (2, 2) ∧
    LatestRow (points [0, 2, 1]) 2 ∧ ¬ LatestRow (next [0, 2, 1] 1) 2 ∧
    leftExternal (points [0, 2, 1]) 0 = none ∧
    leftExternal (next [0, 2, 1] 1) 0 = none ∧
    rightExternal (points [0, 2, 1]) 0 = some 2 ∧
    rightExternal (next [0, 2, 1] 1) 0 = some 1 ∧
    rightExternal (points [0, 2, 1]) 2 = none ∧
    rightExternal (next [0, 2, 1] 1) 2 = none ∧
    leftExternal (points [0, 2, 1]) 2 = some 0 ∧
    leftExternal (next [0, 2, 1] 1) 2 = some 1 := by decide

example : itemAmount eight 0 [0, 2, 1, 1] (next [0, 2, 1] 1) 0 ≤
    itemAmount eight 0 [0, 2, 1, 1] (points [0, 2, 1]) 0 :=
  Unaccessed.Results.external_change eight 0 [0, 2, 1, 1]
    (n := 8) (q := (0, 2)) (by decide) (by unfold History; decide) (by decide) (by decide)
example : itemAmount eight 0 [0, 2, 1, 1] (next [0, 2, 1] 1) 2 ≤
    itemAmount eight 0 [0, 2, 1, 1] (points [0, 2, 1]) 2 :=
  Unaccessed.Results.external_change eight 0 [0, 2, 1, 1]
    (n := 8) (q := (2, 2)) (by decide) (by unfold History; decide) (by decide) (by decide)
example : totalAmount eight 0 [0, 2, 1, 1] (next [0, 2, 1] 1) {0, 2} ≤
    totalAmount eight 0 [0, 2, 1, 1] (points [0, 2, 1]) {0, 2} :=
  Unaccessed.Results.external_sum eight 0 [0, 2, 1, 1]
    (n := 8) (by decide) (by unfold History; decide) {0, 2} (by decide) (by decide)

-- With both external neighbors defined, the moving-side neighbor may
-- move strictly inward while the other neighbor stays put.
example : External (points [5, 0, 4, 3]) (4, 3) ∧
    greedySweep 4 1 (points [5, 0, 4, 3]) = {0, 1, 3} ∧
    leftExternal (points [5, 0, 4, 3]) 4 = some 0 ∧
    rightExternal (points [5, 0, 4, 3]) 4 = some 5 ∧
    leftExternal (next [5, 0, 4, 3] 1) 4 = some 3 ∧
    rightExternal (next [5, 0, 4, 3] 1) 4 = some 5 := by decide
example : ∃ u v, leftExternal (next [5, 0, 4, 3] 1) 4 = some u ∧
    rightExternal (next [5, 0, 4, 3] 1) 4 = some v ∧
    0 ≤ u ∧ u < 4 ∧ 4 < v ∧ v ≤ 5 :=
  Unaccessed.Results.neighbor_interval (greedySweep 4 1 (points [5, 0, 4, 3]))
    (n := 8) (by unfold History; decide) (by decide) (by decide) (by decide)
example : itemAmount eight 0 [5, 0, 4, 3, 1] (next [5, 0, 4, 3] 1) 4 ≤
    itemAmount eight 0 [5, 0, 4, 3, 1] (points [5, 0, 4, 3]) 4 :=
  Unaccessed.Results.external_change eight 0 [5, 0, 4, 3, 1]
    (n := 8) (q := (4, 3)) (by decide) (by unfold History; decide) (by decide) (by decide)

-- The next search destroys the old glancing direction without accessing
-- the red item. Its selected value and color remain unchanged.
example : Glancing (points [0, 2, 1, 0]) (1, 2) ∧
    Internal (next [0, 2, 1, 0] 4) (1, 2) ∧
    1 ∉ greedySweep 4 4 (points [0, 2, 1, 0]) ∧
    itemColor eight 0 [0, 2, 1, 0, 4] (points [0, 2, 1, 0]) 1 = some .red ∧
    itemAmount eight 0 [0, 2, 1, 0, 4] (points [0, 2, 1, 0]) 1 = 3 ∧
    itemAmount eight 0 [0, 2, 1, 0, 4] (next [0, 2, 1, 0] 4) 1 = 3 := by decide
example : itemColor eight 0 [0, 2, 1, 0, 4] (next [0, 2, 1, 0] 4) 1 = some .red ∧
    itemAmount eight 0 [0, 2, 1, 0, 4] (next [0, 2, 1, 0] 4) 1 =
      itemAmount eight 0 [0, 2, 1, 0, 4] (points [0, 2, 1, 0]) 1 :=
  Unaccessed.Results.red_unchanged eight 0 [0, 2, 1, 0, 4]
    (greedySweep 4 4 (points [0, 2, 1, 0])) (n := 8)
    (by unfold History; decide) (by decide) (by decide)

end RotationBST.Tests.GreedyUnaccessedPotential
