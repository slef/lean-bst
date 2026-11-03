module

import RotationBST.Audit.Check
public import RotationBST.Models.Labelled.Ordering.AbstractBridge

@[expose] public section

/-! The textbook BST ordering invariant is given explicitly in
`Definitions/Abstract`. Together with the representation theorems, these results
justify using shapes for BSTs on any fixed strictly ordered key list. -/
namespace RotationBST.Representation

variable {α : Type} [Preorder α]

/-- Local left/root/right inequalities are equivalent to increasing inorder traversal. -/
theorem ordered_iff (t : LabelledTree α) : t.Ordered ↔ t.inorder.Pairwise (· < ·) :=
  OrderingBridge.ordered_iff t

/-- Every shape represents exactly one BST on a prescribed increasing key list. -/
theorem ordered_labels_exist_unique (shape : Tree) (keys : List α)
    (length : keys.length = shape.size) (increasing : keys.Pairwise (· < ·)) :
    ∃! t : LabelledTree α, t.erase = shape ∧ t.inorder = keys ∧ t.Ordered :=
  OrderingBridge.exists_unique shape keys length increasing

/-- Canonical consecutive-rank labellings satisfy the textbook invariant. -/
theorem ordered_label (t : Tree) (lo : Nat) : (t.labelFrom lo).Ordered :=
  OrderingBridge.ordered_label t lo

/-- Every legal rotation trace preserves the invariant in both directions. -/
theorem rotations_preserve_order {s t : LabelledTree α} {k : Nat}
    (rotations : LabelledTree.Rotations s t k) : s.Ordered ↔ t.Ordered :=
  OrderingBridge.ordered_rotations rotations

end RotationBST.Representation

#check_bst_abstract RotationBST.Representation allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Labelled.Ordering.Definitions.Abstract]
