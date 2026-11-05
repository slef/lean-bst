module

public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyColorCounts
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential Geometric.GreedyASS.Potential.Counting

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def sixteen : Tree := .node eight eight
private def actual : Finset Point := fill greedySweep 0 ∅ [4, 6, 2, 2, 5, 6]

-- An actual GreedyASS history attains the two-purple bound in one component.
example : purpleKeys eight 0 [4, 6, 2, 2, 5, 6] actual ⟨4, pair⟩ = {4, 5} := by decide
example : (blueKeys eight 0 ([4, 6, 2, 2, 5] ++ [6]) actual ⟨4, pair⟩).card ≤ 4 ∧
    (purpleKeys eight 0 ([4, 6, 2, 2, 5] ++ [6]) actual ⟨4, pair⟩).card ≤ 2 :=
  Geometric.GreedyASS.Potential.Counting.Results.counts eight 0 [4, 6, 2, 2, 5] 6
    (n := 8) (by decide) (by unfold History; decide) (by decide)

-- Synthetic ASS snapshots test the stronger geometric theorem independently
-- of a particular request execution. The two top corners must stay blue even
-- when green equals blue; omitting their exception would miss two blue items.
private def corners : Finset Point := row 0 (Finset.range 8) ∪ row 1 {1, 6}
example : ASS corners ∧ blueKeys sixteen 0 [0, 8] corners ⟨0, eight⟩ = {0, 1, 6, 7} ∧
    leftBlueKeys sixteen 0 [0, 8] corners ⟨0, eight⟩ = {0, 1} ∧
    rightBlueKeys sixteen 0 [0, 8] corners ⟨0, eight⟩ = {6, 7} := by decide
example : green sixteen 0 corners 1 = (5 : Nat) ∧ currentBlue sixteen 0 [0, 8] 1 = 5 ∧
    itemColor sixteen 0 [0, 8] corners 1 = some .blue := by decide
example : (blueKeys sixteen 0 ([0] ++ [8]) corners ⟨0, eight⟩).card ≤ 4 ∧
    (purpleKeys sixteen 0 ([0] ++ [8]) corners ⟨0, eight⟩).card ≤ 2 :=
  Geometric.GreedyASS.Potential.Counting.Results.counts sixteen 0 [0] 8
    (n := 16) (by decide) (by unfold History; decide) (by decide)

-- Different latest-access times exercise the geometric side-witness argument.
private def rightRow : Finset Point := row 0 (Finset.range 8) ∪ row 1 {4, 5, 6, 7}
private def leftRow : Finset Point := row 0 (Finset.range 8) ∪ row 1 {0, 1, 2}
example : ∃ a b, leftNeighbor rightRow (2, 0) = some a ∧ rightNeighbor rightRow (2, 0) = some b ∧
    1 ≤ a ∧ a < 2 ∧ 2 < b ∧ b ≤ 5 :=
  Geometric.GreedyASS.Potential.Counting.Results.glancing_neighbors
    (p := (1, 0)) (q := (2, 0)) (r := (5, 1))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : ∃ a b, leftNeighbor leftRow (5, 0) = some a ∧ rightNeighbor leftRow (5, 0) = some b ∧
    1 ≤ a ∧ a < 5 ∧ 5 < b ∧ b ≤ 6 :=
  Geometric.GreedyASS.Potential.Counting.Results.glancing_neighbors
    (p := (1, 1)) (q := (5, 0)) (r := (6, 0))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
example : color sixteen 0 ([0] ++ [8]) rightRow (2, 0) = some .red :=
  Geometric.GreedyASS.Potential.Counting.Results.red_middle sixteen 0 [0] 8
    (n := 16) (c := ⟨0, eight⟩) (p := (1, 0)) (q := (2, 0)) (r := (5, 1))
    (by decide) (by unfold History; decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- Changing the forest before adding a row uses the old point set and the
-- extended purple history, rather than assuming the final row already exists.
example : (blueKeys eight 0 ([4, 6, 2, 2, 5, 6] ++ [0]) actual ⟨4, quad⟩).card ≤ 4 ∧
    (purpleKeys eight 0 ([4, 6, 2, 2, 5, 6] ++ [0]) actual ⟨4, quad⟩).card ≤ 2 :=
  Geometric.GreedyASS.Potential.Counting.Results.intermediate eight 0 [4, 6, 2, 2, 5, 6] 0
    (n := 8) (by decide) (by unfold History; decide) (by decide)

example : blueKeys .nil 0 [0] {(0, 0)} ⟨0, .nil⟩ = {0} ∧
    purpleKeys .nil 0 [0] {(0, 0)} ⟨0, .nil⟩ = ∅ := by decide

end RotationBST.Tests.GreedyColorCounts
