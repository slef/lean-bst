module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Abstract
public import RotationBST.Algorithms.GreedyASS.Potential.PhaseTwo.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyPhaseTwo
open Geometric Geometric.GreedyASS Geometric.GreedyASS.Items
open Geometric.GreedyASS.Reference Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def prior : List Nat := [3, 5, 4, 3]
private def current : List Nat := prior ++ [5]

-- The current blue value is too small to cover red. An earlier search
-- in the purple maximum supplies the missing credit. The untouched item
-- changes from purple glancing to red internal at an exact tie.
example : RightGlancing (Virgin.points prior) (4, 2) ∧
    Internal (Virgin.points current) (4, 2) ∧
    Virgin.keys prior 5 = {3, 5} ∧
    blue eight 0 5 4 = 2 ∧ purple eight 0 current 2 4 = 4 ∧
    red eight 0 (Virgin.points current) (4, 2) = WithTop.some 4 ∧
    itemColor eight 0 current (Virgin.points prior) 4 = some .purple ∧
    itemColor eight 0 current (Virgin.points current) 4 = some .red ∧
    itemAmount eight 0 current (Virgin.points prior) 4 = 4 ∧
    itemAmount eight 0 current (Virgin.points current) 4 = 4 := by decide
example : red eight 0 (Virgin.points current) (4, 2) ≤
    WithTop.some (purple eight 0 current 2 4) :=
  Unaccessed.Results.internal_cover eight 0 current (n := 8) (by decide) (by decide)
example : itemAmount eight 0 current (Virgin.points current) 4 ≤
    itemAmount eight 0 current (Virgin.points prior) 4 :=
  Unaccessed.Results.untouched_change eight 0 prior 5 (n := 8) (by decide) (by decide)

-- The mirrored transition requires the opposite historical search.
example : LeftGlancing (Virgin.points [4, 2, 3, 4]) (3, 2) ∧
    Internal (Virgin.points [4, 2, 3, 4, 2]) (3, 2) ∧
    3 ∉ Virgin.keys [4, 2, 3, 4] 2 ∧
    blue eight 0 2 3 = 2 ∧ purple eight 0 [4, 2, 3, 4, 2] 2 3 = 4 ∧
    itemColor eight 0 [4, 2, 3, 4, 2] (Virgin.points [4, 2, 3, 4]) 3 = some .purple ∧
    itemColor eight 0 [4, 2, 3, 4, 2] (Virgin.points [4, 2, 3, 4, 2]) 3 = some .red := by decide
example : itemAmount eight 0 [4, 2, 3, 4, 2] (Virgin.points [4, 2, 3, 4, 2]) 3 ≤
    itemAmount eight 0 [4, 2, 3, 4, 2] (Virgin.points [4, 2, 3, 4]) 3 :=
  Unaccessed.Results.untouched_change eight 0 [4, 2, 3, 4] 2 (n := 8) (by decide) (by decide)

-- The untouched sum includes five unseen columns, all with zero amount.
example : totalAmount eight 0 current (Virgin.points prior) (Finset.range 8 \ Virgin.keys prior 5) = 4 ∧
    totalAmount eight 0 current (Virgin.points current) (Finset.range 8 \ Virgin.keys prior 5) = 4 ∧
    totalAmount eight 0 current (Virgin.points prior) (Finset.range 8) = 10 ∧
    totalAmount eight 0 current (Virgin.points current) (Finset.range 8) = 10 ∧
    coloredKeys eight 0 current (Virgin.points current) (Virgin.keys prior 5) .blue = {3, 5} ∧
    coloredKeys eight 0 current (Virgin.points current) (Virgin.keys prior 5) .purple = ∅ ∧
    unseenKeys (Virgin.points prior) (Virgin.keys prior 5) = ∅ := by decide
example : totalAmount eight 0 current (Virgin.points current) (Finset.range 8 \ Virgin.keys prior 5) ≤
    totalAmount eight 0 current (Virgin.points prior) (Finset.range 8 \ Virgin.keys prior 5) :=
  Unaccessed.Results.untouched_sum eight 0 prior 5 (n := 8) (by decide) _
    (fun _ hx => (Finset.mem_sdiff.mp hx).2)

-- Instantiate the complete whole-universe Phase-II theorem, including
-- virgin roots, on a history with a purple-to-internal transition.
example : (Virgin.keys prior 5).card +
      totalAmount eight 0 current (Virgin.points current) (Finset.range 8) +
      Virgin.after eight 0 prior 5 ≤
    totalAmount eight 0 current (Virgin.points prior) (Finset.range 8) +
      Virgin.before eight 0 prior 5 + 24 +
      3 * (unseenKeys (Virgin.points prior) (Virgin.keys prior 5)).card :=
  PhaseTwo.Results.step eight 0 prior 5 (by decide)

-- Empty history retains first-access credit, and an offset reference
-- interval uses the same theorem without assuming ranks start at zero.
example : (Virgin.keys [] 4).card +
      totalAmount eight 0 [4] (Virgin.points [4]) (Finset.range 8) + Virgin.after eight 0 [] 4 ≤
    totalAmount eight 0 [4] (Virgin.points []) (Finset.range 8) + Virgin.before eight 0 [] 4 + 24 +
      3 * (unseenKeys (Virgin.points []) (Virgin.keys [] 4)).card :=
  PhaseTwo.Results.step eight 0 [] 4 (by decide)
example : (Virgin.keys [11, 13, 12, 11] 13).card +
      totalAmount eight 8 [11, 13, 12, 11, 13] (Virgin.points [11, 13, 12, 11, 13]) (Finset.range 16) +
      Virgin.after eight 8 [11, 13, 12, 11] 13 ≤
    totalAmount eight 8 [11, 13, 12, 11, 13] (Virgin.points [11, 13, 12, 11]) (Finset.range 16) +
      Virgin.before eight 8 [11, 13, 12, 11] 13 + 24 +
      3 * (unseenKeys (Virgin.points [11, 13, 12, 11]) (Virgin.keys [11, 13, 12, 11] 13)).card :=
  PhaseTwo.Results.step eight 8 [11, 13, 12, 11] 13 (by decide)

end RotationBST.Tests.GreedyPhaseTwo
