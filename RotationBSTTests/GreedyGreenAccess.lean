module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Abstract
public import RotationBST.Algorithms.GreedyASS.Items.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyGreenAccess
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def points (xs : List Nat) : Finset Point := fill greedySweep 0 ∅ xs
private def next (xs : List Nat) (searched : Nat) : Finset Point :=
  points xs ∪ row xs.length (greedySweep xs.length searched (points xs))

-- A right-external old green item brings both of its external neighbors
-- into the new row and loses one unit of potential.
example : RightExternal (points [3, 2, 1, 0]) (2, 2) ∧
    ¬ LatestRow (points [3, 2, 1, 0]) 2 ∧
    leftExternal (points [3, 2, 1, 0]) 2 = some 1 ∧
    rightExternal (points [3, 2, 1, 0]) 2 = some 3 ∧
    greedySweep 4 6 (points [3, 2, 1, 0]) = {1, 2, 3, 6} := by decide
example : itemColor eight 0 [3, 2, 1, 0, 6] (points [3, 2, 1, 0]) 2 = some .green ∧
    itemAmount eight 0 [3, 2, 1, 0, 6] (points [3, 2, 1, 0]) 2 = 4 ∧
    itemColor eight 0 [3, 2, 1, 0, 6] (next [3, 2, 1, 0] 6) 2 = some .red ∧
    itemAmount eight 0 [3, 2, 1, 0, 6] (next [3, 2, 1, 0] 6) 2 = 3 := by decide
example : itemAmount eight 0 [3, 2, 1, 0, 6] (next [3, 2, 1, 0] 6) 2 + 1 ≤
    itemAmount eight 0 [3, 2, 1, 0, 6] (points [3, 2, 1, 0]) 2 :=
  Accessed.Results.green_change eight 0 [3, 2, 1, 0] 6
    (n := 8) (by decide) (by unfold History; decide) (by decide) (by decide) (by decide)

example : itemColor eight 0 [3, 2, 1, 0, 6] (next [3, 2, 1, 0] 6) 2 = some .red ∧
    itemAmount eight 0 [3, 2, 1, 0, 6] (next [3, 2, 1, 0] 6) 2 + 1 =
      itemAmount eight 0 [3, 2, 1, 0, 6] (points [3, 2, 1, 0]) 2 :=
  Accessed.Results.green_exact_change eight 0 [3, 2, 1, 0] 6
    (n := 8) (by decide) (by unfold History; decide) (by decide) (by decide) (by decide)

-- The opposite exposed chain gives the same decrease. Repeated searches
-- make the geometric latest row differ from the green item's old row.
example : LeftExternal (points [5, 6, 7, 7]) (6, 2) ∧
    ¬ LatestRow (points [5, 6, 7, 7]) 2 ∧
    itemColor eight 0 [5, 6, 7, 7, 3] (points [5, 6, 7, 7]) 6 = some .green ∧
    itemAmount eight 0 [5, 6, 7, 7, 3] (points [5, 6, 7, 7]) 6 = 4 ∧
    itemAmount eight 0 [5, 6, 7, 7, 3] (next [5, 6, 7, 7] 3) 6 = 3 := by decide
example : itemAmount eight 0 [5, 6, 7, 7, 3] (next [5, 6, 7, 7] 3) 6 + 1 ≤
    itemAmount eight 0 [5, 6, 7, 7, 3] (points [5, 6, 7, 7]) 6 :=
  Accessed.Results.green_change eight 0 [5, 6, 7, 7] 3
    (n := 8) (by decide) (by unfold History; decide) (by decide) (by decide) (by decide)

example : itemColor eight 0 [5, 6, 7, 7, 3] (next [5, 6, 7, 7] 3) 6 = some .red ∧
    itemAmount eight 0 [5, 6, 7, 7, 3] (next [5, 6, 7, 7] 3) 6 + 1 =
      itemAmount eight 0 [5, 6, 7, 7, 3] (points [5, 6, 7, 7]) 6 :=
  Accessed.Results.green_exact_change eight 0 [5, 6, 7, 7] 3
    (n := 8) (by decide) (by unfold History; decide) (by decide) (by decide) (by decide)

-- No first access is present here. Four accesses and final potential 13
-- equal old potential 14 plus the three new blue/purple items.
private def history : List Nat := [6, 3, 2, 1, 0]
private def accessed : Finset Nat := greedySweep history.length 6 (points history)
example : accessed = {1, 2, 3, 6} ∧ unseenKeys (points history) accessed = ∅ ∧
    totalAmount eight 0 (history ++ [6]) (points history) accessed = 14 ∧
    totalAmount eight 0 (history ++ [6]) (next history 6) accessed = 13 ∧
    coloredKeys eight 0 (history ++ [6]) (next history 6) accessed .blue = {1, 6} ∧
    coloredKeys eight 0 (history ++ [6]) (next history 6) accessed .purple = {3} := by decide
example : accessed.card + totalAmount eight 0 (history ++ [6]) (next history 6) accessed ≤
    totalAmount eight 0 (history ++ [6]) (points history) accessed +
      (coloredKeys eight 0 (history ++ [6]) (next history 6) accessed .blue).card +
      (coloredKeys eight 0 (history ++ [6]) (next history 6) accessed .purple).card +
      3 * (unseenKeys (points history) accessed).card :=
  Accessed.Results.whole_row eight 0 history 6
    (n := 8) (by decide) (by unfold History; decide) (by decide)

-- The full-row theorem also retains its first-access allowance on empty
-- history; it does not assign an artificial old green or red color.
example :
    let keys := greedySweep 0 3 ∅
    let Q := row 0 keys
    keys.card + totalAmount eight 0 [3] Q keys ≤ totalAmount eight 0 [3] ∅ keys +
      (coloredKeys eight 0 [3] Q keys .blue).card +
      (coloredKeys eight 0 [3] Q keys .purple).card + 3 * (unseenKeys ∅ keys).card := by
  simpa only [Finset.empty_union, List.length_nil, List.nil_append] using Accessed.Results.whole_row eight 0 [] 3
    (n := 8) (P := ∅) (by simp [ASS]) (by simp [History]) (by simp)

example : ∃ p q, LeftExternal (points history) p ∧ RightExternal (points history) q ∧
    LatestRow (points history) p.2 ∧ q.2 = p.2 :=
  Geometric.GreedyASS.Items.Results.latest_corners (by decide)

end RotationBST.Tests.GreedyGreenAccess
