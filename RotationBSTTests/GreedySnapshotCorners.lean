module

public import RotationBST.Algorithms.GreedyASS.Potential.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Abstract
public import RotationBST.Algorithms.GreedyASS.Items.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedySnapshotCorners
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def sixteen : Tree := .node eight eight
private def points (xs : List Nat) : Finset Point := fill greedySweep 0 ∅ xs
private def old : Finset Point := points [4, 5, 6]
private def next : Finset Point := old ∪ row 3 (greedySweep 3 0 old)

-- Phase I changes the reference search to 0 but has not added row 3.
-- Point (5,2) is still a top corner of the old point set. Its finite green
-- candidate must not override the corner exception, even when tied with blue.
example : External old (5, 2) ∧ LatestRow old 2 ∧
    green eight 0 old 5 = (4 : Nat) ∧ currentBlue eight 0 [4, 5, 6, 0] 5 = 4 ∧
    itemColor eight 0 [4, 5, 6, 0] old 5 = some .blue := by decide

example : color eight 0 [4, 5, 6, 0] old (5, 2) = some .blue ∧
    value eight 0 [4, 5, 6, 0] old (5, 2) = WithTop.some (currentBlue eight 0 [4, 5, 6, 0] 5) :=
  Geometric.GreedyASS.Potential.Results.corner eight 0 [4, 5, 6, 0] (by decide) (by decide)

-- The actual new row touches 5, whose potential stays at four. Miscoloring
-- the old top corner green would incorrectly require a one-unit decrease.
example : greedySweep 3 0 old = {0, 4, 5} ∧
    itemAmount eight 0 [4, 5, 6, 0] old 5 = 4 ∧
    itemAmount eight 0 [4, 5, 6, 0] next 5 = 4 := by decide
example : itemValue eight 0 [4, 5, 6, 0] next 5 ≤ itemValue eight 0 [4, 5, 6, 0] old 5 :=
  (Accessed.Results.blue_change eight 0 [4, 5, 6] 0 _
    (n := 8) (by unfold History; decide) (by decide) (by decide)).1

-- This larger component makes green strictly smaller than blue. Ignoring
-- the old corner would manufacture a potential increase from four to five.
private def farther : Finset Point := points [8, 9, 10]
example : LatestRow farther 2 ∧ green sixteen 0 farther 9 = (4 : Nat) ∧
    currentBlue sixteen 0 [8, 9, 10, 0] 9 = 5 ∧
    itemColor sixteen 0 [8, 9, 10, 0] farther 9 = some .blue ∧
    itemAmount sixteen 0 [8, 9, 10, 0] farther 9 = 5 ∧
    itemAmount sixteen 0 [8, 9, 10, 0] (farther ∪ row 3 (greedySweep 3 0 farther)) 9 = 5 := by decide

-- Latest-row status depends on the point set, even when the reference
-- history is much longer. On a completed row it agrees with the timestamp.
example (searches : List Nat) : color eight 0 searches old (5, 2) = some .blue :=
  (Geometric.GreedyASS.Potential.Results.corner eight 0 searches (by decide) (by decide)).1
example : LatestRow next (5, 3).2 ↔ (5, 3).2 = 3 :=
  Geometric.GreedyASS.Items.Results.latest_row (greedySweep 3 0 old)
    (n := 8) (by unfold History; decide) (by decide) (by decide)
example : ¬ LatestRow next 2 ∧ LatestRow next 3 := by decide

-- Only the two old top corners receive this exception; an older external
-- point with finite green value still uses the minimum rule.
example : itemColor eight 0 [0, 1, 2, 4] (points [0, 1, 2, 4]) 1 = some .green ∧
    ¬ LatestRow (points [0, 1, 2, 4]) 2 := by decide

-- The corrected intermediate coloring retains the per-component counts.
example :
    (Counting.blueKeys sixteen 0 ([8, 9, 10] ++ [0]) farther ⟨8, eight⟩).card ≤ 4 ∧
      (Counting.purpleKeys sixteen 0 ([8, 9, 10] ++ [0]) farther ⟨8, eight⟩).card ≤ 2 :=
  Counting.Results.intermediate sixteen 0 [8, 9, 10] 0
    (n := 16) (by decide) (by unfold History; decide) (by decide)

end RotationBST.Tests.GreedySnapshotCorners
