module

public import RotationBST.Structures.FingerHand.Definitions.Abstract
public import RotationBST.Models.Labelled.Labelling
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.FingerHand

theorem markedCount_eq_filter (marks : Finset Nat) (t : Tree) (lo : Nat) :
    markedCount marks t lo = ((t.labelFrom lo).inorder.filter (· ∈ marks)).length := by
  induction t generalizing lo with
  | nil => rfl
  | node l r ihl ihr =>
    simp only [markedCount, Tree.labelFrom, LabelledTree.inorder, List.filter_append,
      List.length_append, List.filter_cons, ihl, ihr]
    split <;> simp_all
    omega

theorem markedCount_le_card (marks : Finset Nat) (t : Tree) (lo : Nat) : markedCount marks t lo ≤ marks.card := by
  rw [markedCount_eq_filter, Representation.Bridge.inorder_label]
  have hd : ((List.range' lo t.size).filter (· ∈ marks)).Nodup := (List.nodup_range').filter _
  rw [← List.toFinset_card_of_nodup hd]
  apply Finset.card_le_card
  intro a ha
  have h := (List.mem_filter.mp (List.mem_toFinset.mp ha)).2
  simpa using h

/-- Every nonempty compressed hand has at most twice as many vertices as
retained terminals, minus one. No unmarked unary vertex is counted. -/
theorem compress_size_invariant (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (compress marks t lo).erase.size + (if compress marks t lo = .nil then 0 else 1) ≤
      2 * markedCount marks t lo ∧
      (compress marks t lo = .nil ↔ markedCount marks t lo = 0) := by
  induction t generalizing lo with
  | nil => simp [compress, markedCount, LabelledTree.erase, Tree.size]
  | node l r ihl ihr =>
    have hL := ihl lo
    have hR := ihr (lo + l.size + 1)
    rw [compress, markedCount]
    by_cases hm : lo + l.size ∈ marks <;>
      cases hl : compress marks l lo <;> cases hr : compress marks r (lo + l.size + 1) <;>
      simp [hm, hl, hr, LabelledTree.erase, Tree.size] at hL hR ⊢ <;> omega

theorem compress_size (marks : Finset Nat) (t : Tree) (lo : Nat) :
    (compress marks t lo).erase.size ≤ 2 * marks.card := by
  have h := (compress_size_invariant marks t lo).1
  have hc := markedCount_le_card marks t lo
  omega

end RotationBST.FingerHand
