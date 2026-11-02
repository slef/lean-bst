module

import RotationBST.AbstractAudit.Check
public import RotationBST.Representation.Ordering.Abstract
public import RotationBST.Representation.Sequences

@[expose] public section

/-! # Why shapes suffice

Read together with `Model/Abstract.lean`, which contains all the elementary tree
and rotation definitions used here. Keys are normalized to consecutive inorder
ranks; this file does not claim a pointer-cost simulation.
-/
namespace RotationBST.Representation

variable {α : Type} {s t : LabelledTree α} {k : Nat}

/-- Forgetting the canonical labels recovers the original shape. -/
theorem erase_label (t : Tree) (lo : Nat) : (t.labelFrom lo).erase = t :=
  Bridge.erase_label t lo

/-- The canonical labels are exactly the keys `lo, …, lo + size - 1`, in order. -/
theorem inorder_label (t : Tree) (lo : Nat) :
    (t.labelFrom lo).inorder = List.range' lo t.size :=
  Bridge.inorder_label t lo

/-- Every BST on these consecutive keys is recovered from its shape.
Together with `erase_label`, this gives both directions of the correspondence. -/
theorem reconstruct (t : LabelledTree Nat) (lo : Nat)
    (h : t.inorder = List.range' lo t.erase.size) :
    t.erase.labelFrom lo = t :=
  Bridge.reconstruct t lo h

/-- More generally, shape and inorder key list uniquely determine a labelled tree. -/
theorem labels_unique (s t : LabelledTree α)
    (shape : s.erase = t.erase) (keys : s.inorder = t.inorder) : s = t :=
  Bridge.ext s t shape keys

/-- A shape rotation is exactly a labelled rotation under canonical labelling. -/
theorem rotation_iff (s t : Tree) (lo : Nat) :
    Rotate s t ↔ LabelledTree.Rotate (s.labelFrom lo) (t.labelFrom lo) :=
  Bridge.rotation_iff s t lo

/-- Rotations preserve every key and its inorder position, even with arbitrary labels. -/
theorem rotation_preserves_keys (h : LabelledTree.Rotate s t) :
    s.inorder = t.inorder :=
  Bridge.inorder_rotate h

/-- Whole rotation traces correspond with exactly the same cost. -/
theorem rotations_iff (s t : Tree) (k lo : Nat) :
    Rotations s t k ↔ LabelledTree.Rotations (s.labelFrom lo) (t.labelFrom lo) k :=
  Bridge.rotations_iff s t k lo

/-- Accessing implicit rank `x` is exactly accessing explicit key `x` after
labelling by `0, …, size - 1`, with no change to the number of rotations. -/
theorem access_iff (s t : Tree) (x k : Nat) :
    Access s t x k ↔ LabelledTree.Access (s.labelFrom 0) (t.labelFrom 0) x k :=
  Bridge.access_iff s t x k

/-- Any fixed inorder key list labels every shape of the correct size.
Together with `labels_unique`, this is a bijection for arbitrary key types.
A strictly increasing list specializes it to ordinary ordered BSTs. -/
theorem labels_exist (t : Tree) (keys : List α) (length : keys.length = t.size) :
    ∃ u : LabelledTree α, u.erase = t ∧ u.inorder = keys :=
  Bridge.labels_exist t keys length

/-- Exact-cost rotation equivalence for any fixed key list, with no integer-label
or ordering assumption hidden in the theorem. -/
theorem arbitrary_rotations_iff (s t : LabelledTree α) (keys : s.inorder = t.inorder) :
    Rotations s.erase t.erase k ↔ LabelledTree.Rotations s t k :=
  Bridge.arbitrary_rotations_iff s t keys

/-- Distinct arbitrary keys identify the same accesses as their inorder ranks,
with exactly the same rotation count. Strictly ordered key sets are a special case. -/
theorem arbitrary_access_iff (s t : LabelledTree α)
    (keys : s.inorder = t.inorder) (distinct : s.inorder.Nodup)
    (x k : Nat) (valid : x < s.inorder.length) :
    Access s.erase t.erase x k ↔ LabelledTree.Access s t s.inorder[x] k :=
  Bridge.arbitrary_access_iff s t keys distinct x k valid

/-- Whole request sequences translate between ranks and arbitrary distinct keys.
The finite index type makes every requested key valid; costs and endpoints agree. -/
theorem execution_on_keys_iff (keys : List α) (distinct : keys.Nodup)
    (xs : List (Fin keys.length)) (s t : LabelledTree α)
    (hs : s.inorder = keys) (ht : t.inorder = keys) (k : Nat) :
    Execution s.erase (xs.map Fin.val) t.erase k ↔
      LabelledTree.Execution s (xs.map keys.get) t k :=
  Bridge.execution_on_keys_iff keys distinct xs s t hs ht k

end RotationBST.Representation

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Representation allowing [
  RotationBST.Model.Abstract]
