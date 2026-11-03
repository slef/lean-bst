module

public import RotationBST.Models.Labelled.Ordering.Definitions.Abstract
public import RotationBST.Models.Labelled.ArbitraryKeys
public import Mathlib.Data.List.Sort

@[expose] public section

namespace RotationBST.Representation.OrderingBridge

variable {α : Type} [Preorder α]

theorem ordered_iff (t : LabelledTree α) : t.Ordered ↔ t.inorder.Pairwise (· < ·) := by
  induction t with
  | nil => simp [LabelledTree.Ordered, LabelledTree.inorder]
  | node l x r il ir =>
      simp only [LabelledTree.Ordered, LabelledTree.inorder, List.pairwise_append,
        List.pairwise_cons, ← il, ← ir]
      constructor
      · rintro ⟨hl, hr, hleft, hright⟩
        refine ⟨hl, ⟨hright, hr⟩, ?_⟩
        intro y hy z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hleft y hy
        · exact lt_trans (hleft y hy) (hright z hz)
      · rintro ⟨hl, ⟨hright, hr⟩, hcross⟩
        exact ⟨hl, hr, fun y hy => hcross y hy x (by simp), hright⟩

theorem ordered_rotate {s t : LabelledTree α} (h : LabelledTree.Rotate s t) :
    s.Ordered ↔ t.Ordered := by
  rw [ordered_iff, ordered_iff, Bridge.inorder_rotate h]

theorem ordered_rotations {s t : LabelledTree α} {k : Nat} (h : LabelledTree.Rotations s t k) :
    s.Ordered ↔ t.Ordered := by
  rw [ordered_iff, ordered_iff, Bridge.inorder_rotations h]

theorem ordered_label (t : Tree) (lo : Nat) : (t.labelFrom lo).Ordered := by
  rw [ordered_iff, Bridge.inorder_label]
  exact List.pairwise_lt_range' 1 (by decide)

/-- Every shape has exactly one BST with any prescribed strictly increasing
inorder list of the right length. -/
theorem exists_unique (shape : Tree) (keys : List α) (length : keys.length = shape.size)
    (increasing : keys.Pairwise (· < ·)) :
    ∃! t : LabelledTree α, t.erase = shape ∧ t.inorder = keys ∧ t.Ordered := by
  obtain ⟨t, ht, hkeys⟩ := Bridge.labels_exist shape keys length
  refine ⟨t, ⟨ht, hkeys, ?_⟩, ?_⟩
  · rw [ordered_iff, hkeys]; exact increasing
  · intro u hu
    exact Bridge.ext u t (hu.1.trans ht.symm) (hu.2.1.trans hkeys.symm)

end RotationBST.Representation.OrderingBridge
