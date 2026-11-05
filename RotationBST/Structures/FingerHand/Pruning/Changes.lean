module

public import RotationBST.Structures.FingerHand.Pruning.Basic
public import Mathlib.Data.List.Nodup

@[expose] public section
namespace RotationBST.FingerHand

theorem prune_nil_mono {a b : Finset Nat} (sub : a ⊆ b) (t : LabelledTree Nat)
    (empty : prune b t = .nil) : prune a t = .nil :=
  (prune_nil_iff a t).mpr (fun x hx hm => (prune_nil_iff b t).mp empty x hx (sub hm))

/-- Each lost terminal pays for itself and at most one lost branch vertex.
The extra nonempty-root unit handles a whole component disappearing. -/
theorem prune_mass_loss {a b : Finset Nat} (sub : a ⊆ b) (t : LabelledTree Nat) :
    skeletonMass (prune b t) ≤ skeletonMass (prune a t) + 2 * lostMarks b a t := by
  induction t with
  | nil => simp [prune, skeletonMass, lostMarks]
  | node l x r il ir =>
    have nl := prune_nil_mono sub l
    have nr := prune_nil_mono sub r
    by_cases ha : x ∈ a <;> by_cases hb : x ∈ b
    all_goals
      cases al : prune a l <;> cases ar : prune a r <;>
        cases bl : prune b l <;> cases br : prune b r <;>
        simp_all [prune, join, skeletonMass, lostMarks, LabelledTree.erase, Tree.size] <;> omega

theorem prune_size_loss {a b : Finset Nat} (sub : a ⊆ b) (t : LabelledTree Nat) :
    (prune b t).erase.size ≤ (prune a t).erase.size + 2 * lostMarks b a t := by
  have mass := prune_mass_loss sub t
  have nilMono := prune_nil_mono sub t
  cases ha : prune a t <;> cases hb : prune b t <;>
    simp_all [skeletonMass, LabelledTree.erase, Tree.size] <;> omega

theorem lostMarks_erase_le (marks : Finset Nat) (x : Nat) (t : LabelledTree Nat) :
    lostMarks marks (marks.erase x) t ≤ t.inorder.count x := by
  induction t with
  | nil => rfl
  | node l y r il ir =>
    by_cases eq : y = x
    · subst y
      simp only [lostMarks, LabelledTree.inorder, List.count_append, List.count_cons_self,
        Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, and_true]
      split <;> omega
    · simp only [lostMarks, LabelledTree.inorder, List.count_append, List.count_cons,
        Finset.mem_erase]
      simp [eq] at *
      omega

/-- With unique key labels, deleting one mark removes at most two skeleton
vertices, even if the original reference tree is arbitrarily deep. -/
theorem erase_size (marks : Finset Nat) (t : LabelledTree Nat) (distinct : t.inorder.Nodup) (x : Nat) :
    (prune marks t).erase.size ≤ (prune (marks.erase x) t).erase.size + 2 := by
  have loss := prune_size_loss (Finset.erase_subset x marks) t
  have count := lostMarks_erase_le marks x t
  have unique := List.nodup_iff_count_le_one.mp distinct x
  omega

theorem compress_erase_size (marks : Finset Nat) (t : Tree) (lo x : Nat) :
    (compress marks t lo).erase.size ≤ (compress (marks.erase x) t lo).erase.size + 2 := by
  have distinct : (t.labelFrom lo).inorder.Nodup := by
    rw [Representation.Bridge.inorder_label]
    exact List.nodup_range'
  simpa only [prune_label] using erase_size marks (t.labelFrom lo) distinct x

theorem compress_insert_size (marks : Finset Nat) (t : Tree) (lo x : Nat) :
    (compress (insert x marks) t lo).erase.size ≤ (compress marks t lo).erase.size + 2 := by
  by_cases hx : x ∈ marks
  · rw [Finset.insert_eq_of_mem hx]
    omega
  · simpa only [Finset.erase_insert hx] using compress_erase_size (insert x marks) t lo x

end RotationBST.FingerHand
