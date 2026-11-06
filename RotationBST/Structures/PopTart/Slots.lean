module

public import RotationBST.Structures.PopTart.Definitions.Abstract
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

theorem mass_nonnegative {t : WeightedTree} (nonnegative : t.Nonnegative) : 0 ≤ t.mass := by
  induction t with
  | leaf subtree weight => exact nonnegative
  | node l r ihL ihR => exact add_nonneg (ihL nonnegative.1) (ihR nonnegative.2)

/-- Zero-weight slots remain representable, but cannot reduce the total mass. -/
theorem slot_le_mass {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) (nonnegative : t.Nonnegative) :
    0 ≤ weight ∧ weight ≤ t.mass := by
  induction slot with
  | leaf => exact ⟨nonnegative, le_rfl⟩
  | @left l r subtree weight depth slot ih =>
    have found := ih nonnegative.1
    exact ⟨found.1, found.2.trans (le_add_of_nonneg_right (mass_nonnegative nonnegative.2))⟩
  | @right l r subtree weight depth slot ih =>
    have found := ih nonnegative.2
    exact ⟨found.1, found.2.trans (le_add_of_nonneg_left (mass_nonnegative nonnegative.1))⟩

/-- A slot depth is the length of its actual enclosing pointer context. -/
theorem slot_context {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = t.tree := by
  induction slot with
  | leaf => exact ⟨[], rfl, rfl⟩
  | @left l r subtree weight depth slot ih =>
    obtain ⟨cs, length, plugged⟩ := ih
    refine ⟨cs ++ [.left r.tree], by simp [length], ?_⟩
    simp only [Pointer.plug_append, plugged, Pointer.plug]
    rfl
  | @right l r subtree weight depth slot ih =>
    obtain ⟨cs, length, plugged⟩ := ih
    refine ⟨cs ++ [.right l.tree], by simp [length], ?_⟩
    simp only [Pointer.plug_append, plugged, Pointer.plug]
    rfl

/-- Nonempty frozen subtrees can be reached using exactly the outer slot
depth in pointer moves, without rotations or inspecting the frozen subtree. -/
theorem slot_trace {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = t.tree ∧
      Pointer.Trace ⟨t.tree, []⟩ ⟨subtree, cs⟩ depth := by
  obtain ⟨cs, length, plugged⟩ := slot_context slot
  refine ⟨cs, length, plugged, ?_⟩
  cases subtree with
  | nil => exact False.elim (nonempty rfl)
  | node l r =>
    rw [← plugged, ← length]
    exact Pointer.descend cs l r

end RotationBST.PopTart.WeightedTree
