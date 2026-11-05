module

public import RotationBST.Structures.FingerHand.Pruning.Suppression.Normal

@[expose] public section
namespace RotationBST.FingerHand

theorem Contracts.refl (t : LabelledTree Nat) : Contracts t t := by
  induction t with
  | nil => exact .empty _
  | node l x r il ir => exact .node x il ir

theorem Suppress.contracts {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) : Contracts s t := by
  induction h with
  | unaryLeft => exact .left x (.refl _)
  | unaryRight => exact .right x (.refl _)
  | leafLeft => exact .node _ (.empty _) (.refl _)
  | leafRight => exact .node _ (.refl _) (.empty _)
  | inLeft _ ih => exact .node _ ih (.refl _)
  | inRight _ ih => exact .node _ (.refl _) ih

theorem Suppress.nonempty {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) : s ≠ .nil ∧ t ≠ .nil := by
  cases h <;> simp_all

theorem Suppress.contains {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) : x ∈ s.inorder := by
  induction h <;> simp_all [LabelledTree.inorder]

theorem Suppress.other_keys {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) : ∀ y ∈ s.inorder, y ≠ x → y ∈ t.inorder := by
  induction h <;> simp_all only [LabelledTree.inorder, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, false_or] <;> aesop

theorem Suppress.size {marks : Finset Nat} {x : Nat} {s t : LabelledTree Nat}
    (h : Suppress marks x s t) : s.erase.size = t.erase.size + 1 := by
  induction h <;> simp_all [LabelledTree.erase, Tree.size] <;> omega

end RotationBST.FingerHand
