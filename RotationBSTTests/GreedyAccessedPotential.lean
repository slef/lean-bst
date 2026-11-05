module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyAccessedPotential
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def points (xs : List Nat) : Finset Point := fill greedySweep 0 ∅ xs
private def next (xs : List Nat) (searched : Nat) : Finset Point :=
  points xs ∪ row xs.length (greedySweep xs.length searched (points xs))

-- Blue can become purple without losing potential; strict decrease must
-- not be claimed for every accessed item.
example : itemColor eight 0 [0, 1, 0, 2] (points [0, 1, 0]) 1 = some .blue ∧
    itemColor eight 0 [0, 1, 0, 2] (next [0, 1, 0] 2) 1 = some .purple ∧
    itemAmount eight 0 [0, 1, 0, 2] (points [0, 1, 0]) 1 = 3 ∧
    itemAmount eight 0 [0, 1, 0, 2] (next [0, 1, 0] 2) 1 = 3 := by decide

example : itemValue eight 0 [0, 1, 0, 2] (next [0, 1, 0] 2) 1 ≤
    itemValue eight 0 [0, 1, 0, 2] (points [0, 1, 0]) 1 :=
  (Accessed.Results.blue_change eight 0 [0, 1, 0] 2 _
    (n := 8) (by unfold History; decide) (by decide) (by decide)).1

-- The requested key itself may have an old red value. Its searched
-- singleton has blue value two, so it is covered by the same proof.
example : itemColor eight 0 [0, 2, 1, 4, 1] (points [0, 2, 1, 4]) 1 = some .red ∧
    itemAmount eight 0 [0, 2, 1, 4, 1] (points [0, 2, 1, 4]) 1 = 3 ∧
    itemColor eight 0 [0, 2, 1, 4, 1] (next [0, 2, 1, 4] 1) 1 = some .blue ∧
    itemAmount eight 0 [0, 2, 1, 4, 1] (next [0, 2, 1, 4] 1) 1 = 2 := by decide

example : itemValue eight 0 [0, 2, 1, 4, 1] (next [0, 2, 1, 4] 1) 1 ≤
    itemValue eight 0 [0, 2, 1, 4, 1] (points [0, 2, 1, 4]) 1 :=
  (Accessed.Results.red_change eight 0 [0, 2, 1, 4] 1
    (n := 8) (by unfold History; decide) (by decide) (by decide) (by decide)).1

-- A search on the left of an old red item exercises the opposite
-- visibility inequality; this transition need not lose potential.
example : itemValue eight 0 [0, 3, 2, 4, 1] (next [0, 3, 2, 4] 1) 2 ≤
    itemValue eight 0 [0, 3, 2, 4, 1] (points [0, 3, 2, 4]) 2 :=
  (Accessed.Results.red_change eight 0 [0, 3, 2, 4] 1
    (n := 8) (by unfold History; decide) (by decide) (by decide) (by decide)).1

private def purpleHistory : List Nat := [2, 6, 3, 7, 1, 1]
private def redHistory : List Nat := [2, 6, 3, 1, 0, 7, 0, 7]

-- Real sweep executions attain a one-unit loss on both purple-to-red and
-- red-to-red transitions. The historical maximum is not replaced early.
example : itemColor eight 0 (purpleHistory ++ [4]) (points purpleHistory) 2 = some .purple ∧
    itemAmount eight 0 (purpleHistory ++ [4]) (points purpleHistory) 2 = 4 ∧
    itemColor eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) 2 = some .red ∧
    itemAmount eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) 2 = 3 := by decide
example : itemColor eight 0 (redHistory ++ [5]) (points redHistory) 2 = some .red ∧
    itemAmount eight 0 (redHistory ++ [5]) (points redHistory) 2 = 4 ∧
    itemColor eight 0 (redHistory ++ [5]) (next redHistory 5) 2 = some .red ∧
    itemAmount eight 0 (redHistory ++ [5]) (next redHistory 5) 2 = 3 := by decide

-- Four previously colored accesses have total potential 15 before and 14
-- after; the decrease exactly pays for the one new red access.
example : greedySweep purpleHistory.length 4 (points purpleHistory) = {1, 2, 3, 4, 6} ∧
    totalAmount eight 0 (purpleHistory ++ [4]) (points purpleHistory) {1, 2, 3, 6} = 15 ∧
    totalAmount eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) {1, 2, 3, 6} = 14 ∧
    coloredKeys eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) {1, 2, 3, 6} .red = {2} := by decide

example : totalAmount eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) {1, 2, 3, 6} +
    (coloredKeys eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) {1, 2, 3, 6} .red).card ≤
    totalAmount eight 0 (purpleHistory ++ [4]) (points purpleHistory) {1, 2, 3, 6} :=
  Accessed.Results.total eight 0 purpleHistory 4
    (n := 8) (by unfold History; decide) (by decide) {1, 2, 3, 6} (by decide) (by decide)

-- The newly requested 4 is excluded from that old-color sum. Its potential
-- is two, with an additional unit for its actual access cost.
example : unseenKeys (points purpleHistory) (greedySweep purpleHistory.length 4 (points purpleHistory)) = {4} ∧
    itemAmount eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) 4 = 2 := by decide
example : itemAmount eight 0 (purpleHistory ++ [4]) (points purpleHistory) 4 = 0 ∧
    itemAmount eight 0 (purpleHistory ++ [4]) (next purpleHistory 4) 4 ≤ 2 :=
  Accessed.Results.first_access eight 0 purpleHistory 4
    (n := 8) (by unfold History; decide) (by decide) (by decide)

-- Empty history and repeated singleton requests preserve finite amounts.
example : itemAmount eight 0 [3] ∅ 3 = 0 ∧ itemAmount eight 0 [3] (points [3]) 3 = 2 ∧
    itemAmount eight 0 [3, 3] (points [3, 3]) 3 = 2 := by decide

end RotationBST.Tests.GreedyAccessedPotential
