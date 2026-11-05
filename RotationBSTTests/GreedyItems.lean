module

public import RotationBST.Algorithms.GreedyASS.Items.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyItems
open Geometric Geometric.GreedyASS.Items

private def past : Finset Point := fill greedySweep 0 ∅ [0, 2, 1]
private def next : Finset Point := fill greedySweep 3 past [0]
private def finalPoints : Finset Point := fill greedySweep 3 past [0, 2]
private def q : Point := (1, 2)
private theorem history : History 3 3 past := by unfold History; decide

-- Queries distinguish an unseen item from a genuine access at time zero.
example : latest ∅ 0 = none ∧ latest {(0, 0)} 0 = some 0 := by decide
example : latest past 1 = some 2 ∧ latest past 2 = some 2 := by decide
example : leftNeighbor past q = some 0 ∧ rightNeighbor past q = some 2 := by decide
example : leftNeighbor past (0, 2) = none ∧ rightNeighbor past (2, 2) = none := by decide

-- Both glancing directions can hold at once. The location classes themselves
-- are disjoint, but the two directional variants are not separate classes.
example : LeftGlancing past q ∧ RightGlancing past q ∧ ¬ External past q := by decide

-- Actual GreedyASS searches to both sides can make an unaccessed point
-- internal. Its latest time and row neighbors nevertheless remain unchanged.
example : ¬ LeftGlancing next q ∧ RightGlancing next q := by decide
example : Internal finalPoints q ∧ latest finalPoints 1 = some 2 ∧
    leftNeighbor finalPoints q = some 0 ∧ rightNeighbor finalPoints q = some 2 := by decide

example : latest (past ∪ row 3 {0}) 1 = latest past 1 ∧ Active (past ∪ row 3 {0}) q ∧
    leftNeighbor (past ∪ row 3 {0}) q = leftNeighbor past q ∧
    rightNeighbor (past ∪ row 3 {0}) q = rightNeighbor past q ∧
    (External (past ∪ row 3 {0}) q ↔ External past q) :=
  Results.unchanged (q := q) {0} history (by decide) (by decide)

-- The top-corner bound is attained, and a one-key row has one corner even
-- though the point is external in both directions.
example : corners past 3 {0, 1, 2} = {0, 2} := by decide
example : corners past 3 {1} = {1} ∧ corners past 3 ∅ = ∅ := by decide
example : (corners past 3 {0, 1, 2}).card ≤ 2 := Results.top_corners _ history

example : ∃ l r, leftNeighbor past q = some l ∧ rightNeighbor past q = some r :=
  Results.neighbors (by decide) (by decide)

-- Satisfaction is essential for the exposed-quadrant characterization.
-- A same-row extreme can have an upper-left point in a nonsatisfied set.
example : LeftExternal {(1, 0), (0, 1)} (1, 0) ∧ ¬ ASS {(1, 0), (0, 1)} := by decide

-- Changing the latest access invalidates the old-neighbor interpretation.
example : latest (past ∪ row 3 {1}) 1 = some 3 ∧
    leftNeighbor (past ∪ row 3 {1}) (1, 3) = none ∧
    rightNeighbor (past ∪ row 3 {1}) (1, 3) = none := by decide

end RotationBST.Tests.GreedyItems
