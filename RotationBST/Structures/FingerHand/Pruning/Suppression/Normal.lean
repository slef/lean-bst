module

public import RotationBST.Structures.FingerHand.Pruning.Suppression.Definitions.Abstract
public import RotationBST.Structures.FingerHand.Pruning.Contraction

@[expose] public section
namespace RotationBST.FingerHand

theorem prune_reduced (marks : Finset Nat) (t : LabelledTree Nat) : Reduced marks (prune marks t) := by
  induction t with
  | nil => trivial
  | node l x r il ir =>
    by_cases hx : x ∈ marks <;> cases hl : prune marks l <;> cases hr : prune marks r <;>
      simp_all [prune, join, Reduced]

theorem Reduced.fixed {marks : Finset Nat} {t : LabelledTree Nat} (normal : Reduced marks t) :
    prune marks t = t := by
  induction t with
  | nil => rfl
  | node l x r il ir =>
    rw [prune, il normal.1, ir normal.2.1]
    by_cases hx : x ∈ marks
    · simp only [join, hx, ↓reduceIte]
    · have both := normal.2.2.resolve_left hx
      cases l <;> cases r <;> simp_all [join]

theorem Reduced.of_fixed {marks : Finset Nat} {t : LabelledTree Nat} (fixed : prune marks t = t) :
    Reduced marks t := fixed ▸ prune_reduced marks t

theorem compress_reduced (marks : Finset Nat) (t : Tree) (lo : Nat) : Reduced marks (compress marks t lo) := by
  rw [← prune_label]
  exact prune_reduced _ _

/-- Changing a mark absent from this subtree leaves its normal form intact. -/
theorem Reduced.without {marks : Finset Nat} {x : Nat} {t : LabelledTree Nat}
    (normal : Reduced (insert x marks) t) (absent : x ∉ t.inorder) : Reduced marks t := by
  induction t with
  | nil => trivial
  | node l y r il ir =>
    simp only [LabelledTree.inorder, List.mem_append, List.mem_cons, not_or] at absent
    refine ⟨il normal.1 absent.1, ir normal.2.1 absent.2.2, ?_⟩
    rcases normal.2.2 with marked | branch
    · rcases Finset.mem_insert.mp marked with eq | marked
      · exact False.elim (absent.2.1 eq.symm)
      · exact Or.inl marked
    · exact Or.inr branch

end RotationBST.FingerHand
