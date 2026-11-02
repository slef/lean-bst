module

public import RotationBST.Model.Rotations

@[expose] public section

namespace RotationBST.Representation.Bridge

variable {α : Type} {s t : LabelledTree α} {k : Nat}

@[simp] theorem inorder_length (t : LabelledTree α) :
    t.inorder.length = t.erase.size := by
  induction t with
  | nil => rfl
  | node l x r il ir => simp [LabelledTree.inorder, LabelledTree.erase, Tree.size, il, ir, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem erase_label (t : Tree) (lo : Nat) : (t.labelFrom lo).erase = t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir => simp [Tree.labelFrom, LabelledTree.erase, il, ir]

theorem inorder_label (t : Tree) (lo : Nat) :
    (t.labelFrom lo).inorder = List.range' lo t.size := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
      simp only [Tree.labelFrom, LabelledTree.inorder, il, ir, Tree.size]
      rw [show l.size + 1 + r.size = l.size + (r.size + 1) by omega,
        ← List.range'_append_1]
      simp [List.range', Nat.add_comm, Nat.add_left_comm]

/-- Shape plus inorder list determines every node label, without an order assumption. -/
theorem ext (s t : LabelledTree α) (hs : s.erase = t.erase)
    (hi : s.inorder = t.inorder) : s = t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all [LabelledTree.erase]
  | node l x r il ir =>
      cases t with
      | nil => simp [LabelledTree.erase] at hs
      | node a y b =>
          obtain ⟨hl, hr⟩ := Tree.node.inj hs
          have hn : l.inorder.length = a.inorder.length := by simp [hl]
          obtain ⟨hleft, hrest⟩ := List.append_inj hi hn
          obtain ⟨hkey, hright⟩ := List.cons.inj hrest
          cases il a hl hleft
          cases ir b hr hright
          cases hkey
          rfl

theorem reconstruct (t : LabelledTree Nat) (lo : Nat)
    (h : t.inorder = List.range' lo t.erase.size) :
    t.erase.labelFrom lo = t :=
  ext _ _ (erase_label _ _) ((inorder_label _ _).trans h.symm)

theorem erase_rotate (h : LabelledTree.Rotate s t) : Rotate s.erase t.erase := by
  induction h with
  | right => exact .right
  | left => exact .left
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih

theorem label_rotate {s t : Tree} (h : Rotate s t) (lo : Nat) :
    LabelledTree.Rotate (s.labelFrom lo) (t.labelFrom lo) := by
  induction h generalizing lo with
  | right => simp only [Tree.labelFrom, Tree.size, Nat.add_assoc]; exact .right
  | left => simp only [Tree.labelFrom, Tree.size, Nat.add_assoc]; exact .left
  | inLeft h ih =>
      simp only [Tree.labelFrom, h.size_eq]
      exact .inLeft (ih lo)
  | inRight _ ih => exact .inRight (ih _)

theorem inorder_rotate (h : LabelledTree.Rotate s t) : s.inorder = t.inorder := by
  induction h with
  | right => simp [LabelledTree.inorder, List.append_assoc]
  | left => simp [LabelledTree.inorder, List.append_assoc]
  | inLeft _ ih => simp [LabelledTree.inorder, ih]
  | inRight _ ih => simp [LabelledTree.inorder, ih]

theorem rotation_iff (s t : Tree) (lo : Nat) :
    Rotate s t ↔ LabelledTree.Rotate (s.labelFrom lo) (t.labelFrom lo) := by
  constructor
  · exact fun h => label_rotate h lo
  · intro h
    simpa only [erase_label] using erase_rotate h

theorem label_rotations {s t : Tree} (h : Rotations s t k) (lo : Nat) :
    LabelledTree.Rotations (s.labelFrom lo) (t.labelFrom lo) k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (label_rotate h lo) ih

theorem erase_rotations (h : LabelledTree.Rotations s t k) :
    Rotations s.erase t.erase k := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .step (erase_rotate h) ih

theorem rotations_iff (s t : Tree) (k lo : Nat) :
    Rotations s t k ↔ LabelledTree.Rotations (s.labelFrom lo) (t.labelFrom lo) k := by
  constructor
  · exact fun h => label_rotations h lo
  · intro h
    simpa only [erase_label] using erase_rotations h

theorem access_iff (s t : Tree) (x k : Nat) :
    Access s t x k ↔ LabelledTree.Access (s.labelFrom 0) (t.labelFrom 0) x k := by
  unfold Access LabelledTree.Access
  rw [rotations_iff s t k 0]
  cases t <;> simp [Tree.labelFrom]

end RotationBST.Representation.Bridge
