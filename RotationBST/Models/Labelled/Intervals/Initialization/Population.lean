module

public import RotationBST.Models.Labelled.Intervals.Initialization.Definitions.Abstract
public import RotationBST.Models.Labelled.Metadata.Representation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.IntervalMetadata.Initialization

theorem populate_outside (tree : Tree) (lo : Nat) (fields : Nat → Bounds) (x : Nat)
    (outside : x < lo ∨ lo + tree.size ≤ x) : populate tree lo fields x = fields x := by
  induction tree generalizing lo fields with
  | nil => rfl
  | node l r il ir =>
    have offLeft : x < lo ∨ lo + l.size ≤ x := by simp only [Tree.size] at outside; omega
    have offRight : x < lo + l.size + 1 ∨ lo + l.size + 1 + r.size ≤ x := by simp only [Tree.size] at outside; omega
    have different : x ≠ lo + l.size := by simp only [Tree.size] at outside; omega
    rw [populate, ir _ _ offRight, il _ _ offLeft, Function.update_of_ne different]

/-- Initialization changes exactly the finite node fields into their required
interval annotation, independently of their previous contents. -/
theorem populate_label (tree : Tree) (lo : Nat) (fields : Nat → Bounds) :
    Metadata.label (populate tree lo fields) tree lo = label tree lo := by
  induction tree generalizing lo fields with
  | nil => rfl
  | node l r il ir =>
    let rootFields := Function.update fields (lo + l.size) (Bounds.mk lo (lo + (Tree.node l r).size))
    let leftFields := populate l lo rootFields
    have unchangedLeft : Metadata.label (populate r (lo + l.size + 1) leftFields) l lo = Metadata.label leftFields l lo := by
      apply Metadata.label_congr
      intro x low high
      exact populate_outside r _ leftFields x (Or.inl (by omega))
    have rootRight := populate_outside r (lo + l.size + 1) leftFields (lo + l.size) (Or.inl (by omega))
    have rootLeft := populate_outside l lo rootFields (lo + l.size) (Or.inr le_rfl)
    change LabelledTree.node (Metadata.label (populate r (lo + l.size + 1) leftFields) l lo)
      (lo + l.size, populate r (lo + l.size + 1) leftFields (lo + l.size))
      (Metadata.label (populate r (lo + l.size + 1) leftFields) r (lo + l.size + 1)) = _
    change leftFields (lo + l.size) = rootFields (lo + l.size) at rootLeft
    rw [unchangedLeft, rootRight, rootLeft, ir]
    change LabelledTree.node (Metadata.label (populate l lo rootFields) l lo)
      (lo + l.size, rootFields (lo + l.size)) (label r (lo + l.size + 1)) = _
    rw [il]
    simp only [rootFields, Function.update_self, label]

theorem work_formula (tree : Tree) (nonempty : tree ≠ .nil) : work tree + 4 = 8 * tree.size := by
  induction tree with
  | nil => exact False.elim (nonempty rfl)
  | node l r il ir =>
    have left : (if l = .nil then 1 else 5 + work l) = 8 * l.size + 1 := by
      by_cases empty : l = .nil
      · subst l; rfl
      · rw [ite_eq_right empty]; have bound := il empty; omega
    have right : (if r = .nil then 1 else 5 + work r) = 8 * r.size + 1 := by
      by_cases empty : r = .nil
      · subst r; rfl
      · rw [ite_eq_right empty]; have bound := ir empty; omega
    rw [work, left, right, Tree.size]
    omega

theorem work_bound (tree : Tree) : work tree ≤ 8 * tree.size := by
  by_cases empty : tree = .nil
  · subst tree; exact Nat.le_refl _
  · have formula := work_formula tree empty; omega

end RotationBST.IntervalMetadata.Initialization
