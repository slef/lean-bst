module

public import RotationBST.Structures.HeavyPath.Paired.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.Chocolate

private theorem log_mono {small large weight : ℝ}
    (weightPositive : 0 < weight) (slotMass : weight ≤ small) (massBound : small ≤ large) :
    Real.logb 2 (small / weight) ≤ Real.logb 2 (large / weight) := by
  exact Real.logb_le_logb_of_le (by norm_num) (div_pos (lt_of_lt_of_le weightPositive slotMass) weightPositive)
    (div_le_div_of_nonneg_right massBound weightPositive.le)

theorem lower_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.lower.decode subtree weight depth) (positive : 0 < weight) :
    ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  have depthBound := Chocolate.Results.weighted_depth valid.1 slot positive
  have lowerMass := (WeightedTree.Results.slot_le_mass slot (Chocolate.Results.layer_nonnegative valid.1)).2
  have upperNonnegative := WeightedTree.Results.mass_nonnegative (Chocolate.Results.layer_nonnegative valid.2)
  have logarithm := log_mono positive lowerMass
    (show p.lower.decode.mass ≤ p.mass by dsimp [Stacks.mass]; linarith)
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

theorem upper_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.upper.decode.mirror subtree weight depth) (positive : 0 < weight) :
    ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  have reflected := slot.mirror
  rw [WeightedTree.mirror_mirror] at reflected
  have depthBound := Chocolate.Results.weighted_depth valid.2 reflected positive
  have upperMass := (WeightedTree.Results.slot_le_mass reflected (Chocolate.Results.layer_nonnegative valid.2)).2
  have lowerNonnegative := WeightedTree.Results.mass_nonnegative (Chocolate.Results.layer_nonnegative valid.1)
  have logarithm := log_mono positive upperMass
    (show p.upper.decode.mass ≤ p.mass by dsimp [Stacks.mass]; linarith)
  simp only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Access a retained lower off-path subtree from the pair's endpoint root. -/
theorem lower_access {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.lower.decode subtree weight depth)
    (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth + 1 ∧ Pointer.plug cs subtree = p.tree ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨subtree, cs⟩ (depth + 1) ∧
      ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  have whole : WeightedTree.SlotAt (.node p.lower.decode p.upper.decode.mirror) subtree weight (depth + 1) :=
    .left slot
  obtain ⟨cs, length, tree, trace⟩ := WeightedTree.Results.slot_trace whole nonempty
  have physical : (WeightedTree.node p.lower.decode p.upper.decode.mirror).tree = p.tree := by
    change Tree.node p.lower.decode.tree p.upper.decode.mirror.tree = p.tree
    rw [WeightedTree.mirror_tree]
    rfl
  rw [physical] at tree trace
  exact ⟨cs, length, tree, trace, lower_depth valid slot positive⟩

/-- Access a retained upper subtree in its original, unreflected orientation. -/
theorem upper_access {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt p.upper.decode.mirror subtree weight depth)
    (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth + 1 ∧ Pointer.plug cs subtree = p.tree ∧
      Pointer.Trace ⟨p.tree, []⟩ ⟨subtree, cs⟩ (depth + 1) ∧
      ((depth + 1 : Nat) : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  have whole : WeightedTree.SlotAt (.node p.lower.decode p.upper.decode.mirror) subtree weight (depth + 1) :=
    .right slot
  obtain ⟨cs, length, tree, trace⟩ := WeightedTree.Results.slot_trace whole nonempty
  have physical : (WeightedTree.node p.lower.decode p.upper.decode.mirror).tree = p.tree := by
    change Tree.node p.lower.decode.tree p.upper.decode.mirror.tree = p.tree
    rw [WeightedTree.mirror_tree]
    rfl
  rw [physical] at tree trace
  exact ⟨cs, length, tree, trace, upper_depth valid slot positive⟩

end RotationBST.HeavyPath.Paired
