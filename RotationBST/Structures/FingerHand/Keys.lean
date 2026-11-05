module

public import RotationBST.Structures.FingerHand.Size
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.FingerHand

/-- Compression only removes vertices; the remaining keys retain their inorder
order, so the hand is still an ordered, duplicate-free tree of original keys. -/
theorem compress_sublist (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (compress marks t lo).inorder.Sublist (t.labelFrom lo).inorder := by
  induction t generalizing lo with
  | nil => exact .refl _
  | node l r ihl ihr =>
    have hL := ihl lo
    have hR := ihr (lo + l.size + 1)
    have hnode := hL.append (List.Sublist.cons_cons (lo + l.size) hR)
    have hleft := hL.trans (List.sublist_append_left (l.labelFrom lo).inorder
      ((lo + l.size) :: (r.labelFrom (lo + l.size + 1)).inorder))
    have hright := (hR.cons (lo + l.size)).trans
      (List.sublist_append_right (l.labelFrom lo).inorder
        ((lo + l.size) :: (r.labelFrom (lo + l.size + 1)).inorder))
    simp only [Tree.labelFrom, LabelledTree.inorder]
    by_cases hm : lo + l.size ∈ marks
    · simpa only [compress, hm, ↓reduceIte, LabelledTree.inorder] using hnode
    · cases hl : compress marks l lo <;> cases hr : compress marks r (lo + l.size + 1) <;>
        simp only [compress, hm, ↓reduceIte, hl, hr, LabelledTree.inorder] at *
      · exact List.nil_sublist _
      · exact hright
      · exact hleft
      · exact hnode

/-- No marked key in the reference interval is lost during contraction. -/
theorem marked_mem (marks : Finset Nat) (t : Tree) (lo a : Nat)
    (ha : a ∈ (t.labelFrom lo).inorder) (marked : a ∈ marks) :
    a ∈ (compress marks t lo).inorder := by
  induction t generalizing lo with
  | nil => simp [Tree.labelFrom, LabelledTree.inorder] at ha
  | node l r ihl ihr =>
    simp only [Tree.labelFrom, LabelledTree.inorder, List.mem_append, List.mem_cons] at ha
    have hL : a ∈ (l.labelFrom lo).inorder → a ∈ (compress marks l lo).inorder :=
      fun h => ihl lo h
    have hR : a ∈ (r.labelFrom (lo + l.size + 1)).inorder →
        a ∈ (compress marks r (lo + l.size + 1)).inorder := fun h => ihr _ h
    by_cases hm : lo + l.size ∈ marks
    · simp only [compress, hm, ↓reduceIte, LabelledTree.inorder, List.mem_append, List.mem_cons]
      rcases ha with ha | he | ha
      · exact Or.inl (hL ha)
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (hR ha))
    · have hne : a ≠ lo + l.size := by intro he; exact hm (he ▸ marked)
      cases hl : compress marks l lo <;> cases hr : compress marks r (lo + l.size + 1) <;>
        simp only [compress, hm, ↓reduceIte, hl, hr, LabelledTree.inorder] at * <;> aesop

end RotationBST.FingerHand
