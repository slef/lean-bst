module

public import RotationBST.Structures.HeavyPath.Finger.Preservation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger
open PopTart PopTart.WeightedTree

theorem combined_tree (p : Pair) :
    (WeightedTree.node p.lower.decode.mirror p.upper.decode).tree = p.tree := by
  change Tree.node p.lower.decode.mirror.tree p.upper.decode.tree = p.tree
  rw [mirror_tree]
  rfl

theorem located_depth {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) : (depth : ℝ) ≤ 8 + 7 * Real.logb 2 (p.mass / weight) := by
  have swapped : (Paired.Stacks.mk p.upper p.lower).Valid := ⟨valid.2, valid.1⟩
  cases slot with
  | left found =>
    simpa only [Paired.Stacks.mass, Pair.mass, add_comm] using Paired.upper_depth swapped found.forget positive
  | right found =>
    simpa only [Paired.Stacks.mass, Pair.mass, add_comm] using Paired.lower_depth swapped found.forget positive

theorem located_mass {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth) :
    0 ≤ weight ∧ weight ≤ p.mass := by
  have nonnegative : (WeightedTree.node p.lower.decode.mirror p.upper.decode).Nonnegative :=
    ⟨mirror_nonnegative (Chocolate.Results.layer_nonnegative valid.1),
      Chocolate.Results.layer_nonnegative valid.2⟩
  simpa only [WeightedTree.mass, mirror_mass, Pair.mass] using slot_le_mass slot.forget nonnegative

theorem located_key_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (rank : Nat) (inside : rank < subtree.size) :
    (Tree.depth p.tree (offset + rank) : ℝ) ≤
      8 + 7 * Real.logb 2 (p.mass / weight) + Tree.depth subtree rank := by
  have equation := slot.key_depth rank inside
  rw [combined_tree] at equation
  rw [equation, Nat.cast_add]
  have bound := located_depth valid slot positive
  linarith

theorem located_predecessor_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : 0 < offset) :
    (Tree.depth p.tree (offset - 1) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have above := slot.predecessor_depth existsKey
  rw [combined_tree] at above
  have integerBound : Tree.depth p.tree (offset - 1) + 1 ≤ depth := by omega
  have realBound : (Tree.depth p.tree (offset - 1) : ℝ) + 1 ≤ depth := by exact_mod_cast integerBound
  have bound := located_depth valid slot positive
  linarith

theorem located_successor_bound {p : Pair} (valid : p.Valid) {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot (.node p.lower.decode.mirror p.upper.decode) subtree weight offset depth)
    (positive : 0 < weight) (existsKey : offset + subtree.size < p.tree.size) :
    (Tree.depth p.tree (offset + subtree.size) : ℝ) ≤ 7 + 7 * Real.logb 2 (p.mass / weight) := by
  have above := slot.successor_depth (by simpa only [combined_tree] using existsKey)
  rw [combined_tree] at above
  have integerBound : Tree.depth p.tree (offset + subtree.size) + 1 ≤ depth := by omega
  have realBound : (Tree.depth p.tree (offset + subtree.size) : ℝ) + 1 ≤ depth := by exact_mod_cast integerBound
  have bound := located_depth valid slot positive
  linarith

end RotationBST.HeavyPath.Finger
