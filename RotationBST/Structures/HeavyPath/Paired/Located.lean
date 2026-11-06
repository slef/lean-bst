module

public import RotationBST.Structures.HeavyPath.Paired.Access
public import RotationBST.Structures.PopTart.Located.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired
open PopTart PopTart.WeightedTree

private theorem combined_tree (p : Stacks) :
    (WeightedTree.node p.lower.decode p.upper.decode.mirror).tree = p.tree := by
  change Tree.node p.lower.decode.tree p.upper.decode.mirror.tree = p.tree
  rw [mirror_tree]
  rfl

theorem lower_key_depth {p : Stacks} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth p.tree (offset + x) = depth + 1 + Tree.depth subtree x := by
  have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset (depth + 1) :=
    .left slot
  simpa only [combined_tree] using combined.key_depth x inside

theorem upper_key_depth {p : Stacks} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth p.tree (p.lower.decode.tree.size + 1 + offset + x) =
      depth + 1 + Tree.depth subtree x := by
  have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight
      (offset + p.lower.decode.tree.size + 1) (depth + 1) := .right slot
  simpa only [combined_tree, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using combined.key_depth x inside

theorem lower_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (positive : 0 < weight)
    (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x := by
  have bound := lower_depth valid slot.forget positive
  rw [lower_key_depth slot x inside]
  simp only [Nat.cast_add, Nat.cast_one] at bound ⊢
  linarith

theorem upper_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (positive : 0 < weight)
    (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (p.lower.decode.tree.size + 1 + offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x := by
  have bound := upper_depth valid slot.forget positive
  rw [upper_key_depth slot x inside]
  simp only [Nat.cast_add, Nat.cast_one] at bound ⊢
  linarith

/-- The separator after a lower payload is charged to that exact slot. The
last lower slot's successor is the endpoint root, so it is always present. -/
theorem lower_separator_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.lower.decode subtree weight offset depth) (positive : 0 < weight) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset (depth + 1) :=
    .left slot
  have existsKey : offset + subtree.size < (WeightedTree.node p.lower.decode p.upper.decode.mirror).tree.size := by
    have fits := slot.fits
    change offset + subtree.size < p.lower.decode.tree.size + 1 + p.upper.decode.mirror.tree.size
    omega
  have above := combined.successor_depth existsKey
  rw [combined_tree] at above
  have integerBound : Tree.depth p.tree (offset + subtree.size) + 1 ≤ depth + 1 := by omega
  have realBound : (Tree.depth p.tree (offset + subtree.size) : ℝ) + 1 ≤ (depth + 1 : Nat) := by
    exact_mod_cast integerBound
  have slotBound := lower_depth valid slot.forget positive
  linarith

/-- The separator before an upper payload is bounded in the physical,
reflected orientation. Its global rank is lower-size plus the slot offset. -/
theorem upper_separator_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot p.upper.decode.mirror subtree weight offset depth) (positive : 0 < weight) :
    (Tree.depth p.tree (p.lower.decode.tree.size + offset) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have combined : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight
      (offset + p.lower.decode.tree.size + 1) (depth + 1) := .right slot
  have above := combined.predecessor_depth (by omega)
  rw [combined_tree] at above
  have index : offset + p.lower.decode.tree.size + 1 - 1 = p.lower.decode.tree.size + offset := by omega
  rw [index] at above
  have integerBound : Tree.depth p.tree (p.lower.decode.tree.size + offset) + 1 ≤ depth + 1 := by omega
  have realBound : (Tree.depth p.tree (p.lower.decode.tree.size + offset) : ℝ) + 1 ≤ (depth + 1 : Nat) := by
    exact_mod_cast integerBound
  have slotBound := upper_depth valid slot.forget positive
  linarith

/-- A located occurrence in either child uses the physical pair coordinates. -/
theorem located_depth {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) : (depth : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  cases slot with
  | left found => exact lower_depth valid found.forget positive
  | right found => exact upper_depth valid found.forget positive

theorem located_mass {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth) :
    0 ≤ weight ∧ weight ≤ p.mass := by
  have nonnegative : (WeightedTree.node p.lower.decode p.upper.decode.mirror).Nonnegative :=
    ⟨Chocolate.Results.layer_nonnegative valid.1,
      mirror_nonnegative (Chocolate.Results.layer_nonnegative valid.2)⟩
  simpa only [WeightedTree.mass, mirror_mass, Stacks.mass] using slot_le_mass slot.forget nonnegative

theorem located_key_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (x : Nat) (inside : x < subtree.size) :
    (Tree.depth p.tree (offset + x) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree x := by
  have equation := slot.key_depth x inside
  rw [combined_tree] at equation
  rw [equation, Nat.cast_add]
  have bound := located_depth valid slot positive
  linarith

theorem located_successor_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : offset + subtree.size < p.tree.size) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have above := slot.successor_depth (by simpa only [combined_tree] using existsKey)
  rw [combined_tree] at above
  have integerBound : Tree.depth p.tree (offset + subtree.size) + 1 ≤ depth := by omega
  have realBound : (Tree.depth p.tree (offset + subtree.size) : ℝ) + 1 ≤ depth := by
    exact_mod_cast integerBound
  have bound := located_depth valid slot positive
  linarith

theorem located_predecessor_bound {p : Stacks} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode p.upper.decode.mirror) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : 0 < offset) :
    (Tree.depth p.tree (offset - 1) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have above := slot.predecessor_depth existsKey
  rw [combined_tree] at above
  have integerBound : Tree.depth p.tree (offset - 1) + 1 ≤ depth := by omega
  have realBound : (Tree.depth p.tree (offset - 1) : ℝ) + 1 ≤ depth := by
    exact_mod_cast integerBound
  have bound := located_depth valid slot positive
  linarith

end RotationBST.HeavyPath.Paired
