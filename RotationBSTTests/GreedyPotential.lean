module

public import RotationBST.Algorithms.GreedyASS.Potential.Abstract

@[expose] public section
namespace RotationBST.Tests.GreedyPotential
open Geometric Geometric.GreedyASS.Items Geometric.GreedyASS.Reference
open Geometric.GreedyASS.Potential

private def pair : Tree := .node .nil .nil
private def quad : Tree := .node pair pair
private def eight : Tree := .node quad quad
private def points (xs : List Nat) : Finset Point := fill greedySweep 0 ∅ xs

-- Real GreedyASS histories distinguish the two tie priorities.
example : red eight 0 (points [0, 1, 0, 2]) (1, 3) = (3 : Nat) ∧
    purple eight 0 [0, 1, 0, 2] 3 1 = 3 ∧
    color eight 0 [0, 1, 0, 2] (points [0, 1, 0, 2]) (1, 3) = some .purple := by decide

example : green eight 0 (points [0, 1, 2, 4]) 1 = (4 : Nat) ∧
    currentBlue eight 0 [0, 1, 2, 4] 1 = 4 ∧
    color eight 0 [0, 1, 2, 4] (points [0, 1, 2, 4]) (1, 2) = some .green := by decide

-- Purple records earlier forests, not just the current blue value. Access
-- on the newest row resets its interval to a single blue observation.
example : blue eight 0 2 1 = 3 ∧ purple eight 0 [0, 2, 1, 4, 2] 2 1 = 4 ∧
    purple eight 0 [0, 2, 1, 4, 2] 4 1 = 3 := by decide

example : Glancing (points [0, 2, 1, 4]) (1, 2) ∧
    red eight 0 (points [0, 2, 1, 4]) (1, 2) = (3 : Nat) ∧
    color eight 0 [0, 2, 1, 4] (points [0, 2, 1, 4]) (1, 2) = some .red := by decide

-- Green uses neighboring external items, which can be on different rows.
example : externalKeys (points [0, 1, 2, 4]) = {0, 1, 2, 4} ∧
    leftExternal (points [0, 1, 2, 4]) 1 = some 0 ∧
    rightExternal (points [0, 1, 2, 4]) 1 = some 2 := by decide

-- Missing neighbors give infinite candidates, while a searched singleton's
-- selected blue value is finite and counts its root node plus one.
example : green eight 0 (points [3]) 3 = ⊤ ∧ red eight 0 (points [3]) (3, 0) = ⊤ ∧
    color eight 0 [3] (points [3]) (3, 0) = some .blue ∧
    value eight 0 [3] (points [3]) (3, 0) = (2 : Nat) := by decide

-- An old point in a column with a newer access is inactive, not recolored.
example : color eight 0 [0, 0] (points [0, 0]) (0, 0) = none ∧
    value eight 0 [0, 0] (points [0, 0]) (0, 0) = (0 : Nat) := by decide

-- Phase I has already added search 4 to the forest history. Phase II adds
-- its actual sweep row {2,4}, leaving the glancing point and its color fixed.
example : color eight 0 [0, 2, 1, 4] (points [0, 2, 1] ∪ row 3 {2, 4}) (1, 2) =
      color eight 0 [0, 2, 1, 4] (points [0, 2, 1]) (1, 2) ∧
    value eight 0 [0, 2, 1, 4] (points [0, 2, 1] ∪ row 3 {2, 4}) (1, 2) =
      value eight 0 [0, 2, 1, 4] (points [0, 2, 1]) (1, 2) :=
  Geometric.GreedyASS.Potential.Results.glancing_stable eight 0 [0, 2, 1, 4] {2, 4}
    (n := 8) (by unfold History; decide) (by decide) (by decide)

example : value eight 0 [0, 2, 1, 0, 2, 0]
      (points [0, 2, 1, 0, 2] ∪ row 5 {0}) (1, 2) =
    value eight 0 [0, 2, 1, 0, 2, 0] (points [0, 2, 1, 0, 2]) (1, 2) :=
  Geometric.GreedyASS.Potential.Results.internal_stable eight 0 [0, 2, 1, 0, 2, 0] {0}
    (n := 8) (by unfold History; decide) (by decide) (by decide)

example (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) :
    ∃ v : Nat, value t lo searches P q = v :=
  Geometric.GreedyASS.Potential.Results.finite t lo searches P q

-- Intermediate item colors use the latest old row. A newly searched key
-- has no old color and must remain explicit in the partition accounting.
example : itemColor eight 0 [0, 2, 1, 4] (points [0, 2, 1]) 2 = some .blue ∧
    color eight 0 [0, 2, 1, 4] (points [0, 2, 1]) (2, 3) = none ∧
    unseenKeys (points [0, 2, 1]) {2, 4} = {4} ∧
    coloredKeys eight 0 [0, 2, 1, 4] (points [0, 2, 1]) {2, 4} .blue = {2} := by decide

example : unseenKeys (points [0, 1, 2, 4]) {0, 1, 2, 4, 7} = {7} ∧
    coloredKeys eight 0 [0, 1, 2, 4] (points [0, 1, 2, 4]) {0, 1, 2, 4, 7} .green = {1} ∧
    coloredKeys eight 0 [0, 1, 2, 4] (points [0, 1, 2, 4]) {0, 1, 2, 4, 7} .blue = {0, 2, 4} := by decide

example : firstAccesses 0 ∅ [0, 1, 2, 4] = 4 ∧ firstAccesses 0 ∅ [0, 0, 0] = 1 ∧
    firstAccesses 3 (points [0, 1, 2]) [4, 4, 2, 7] = 2 := by decide

example (xs : List Nat) (valid : ∀ x ∈ xs, x < 8) : firstAccesses 0 ∅ xs ≤ 8 := by
  have bound := Geometric.GreedyASS.Potential.Results.startup xs
    (time := 0) (P := ∅) (by simp [History]) (by simp [ASS]) valid
  simpa using bound

end RotationBST.Tests.GreedyPotential
