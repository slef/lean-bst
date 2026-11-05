module

public import RotationBST.Structures.Treap.Random.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Treap.Random

theorem average_empty (w : Nat → ℝ) (f : List Nat → ℝ) : average w ∅ f = f [] := by
  rw [average, ite_eq_left rfl]

theorem average_step (w : Nat → ℝ) (s : Finset Nat) (f : List Nat → ℝ) (hs : s.Nonempty) :
    average w s f = ∑ x ∈ s, w x / (∑ k ∈ s, w k) *
      average w (s.erase x) (fun xs => f (x :: xs)) := by
  rw [average, ite_eq_right hs.ne_empty]
  exact Finset.sum_attach s (fun x : Nat => w x / (∑ k ∈ s, w k) *
    average w (s.erase x) (fun xs => f (x :: xs)))

theorem mass_pos (w : Nat → ℝ) (s : Finset Nat) (hs : s.Nonempty)
    (hw : ∀ x ∈ s, 0 < w x) : 0 < ∑ x ∈ s, w x :=
  Finset.sum_pos hw hs

/-- The finite sampling process has total probability one. -/
theorem average_const (w : Nat → ℝ) (s : Finset Nat) (c : ℝ)
    (hw : ∀ x ∈ s, 0 < w x) : average w s (fun _ => c) = c := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [average_step w s _ hs]
      have he : ∀ x ∈ s, average w (s.erase x) (fun _ => c) = c := by
        intro x hx
        apply ih (s.erase x) (Finset.erase_ssubset hx)
        exact fun k hk => hw k (Finset.mem_of_mem_erase hk)
      rw [Finset.sum_congr rfl (fun x hx => congrArg (fun z => w x / (∑ k ∈ s, w k) * z) (he x hx))]
      rw [← Finset.sum_mul, ← Finset.sum_div, div_self (ne_of_gt (mass_pos w s hs hw)), one_mul]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs, average_empty]

theorem average_add (w : Nat → ℝ) (s : Finset Nat) (f g : List Nat → ℝ) :
    average w s (fun xs => f xs + g xs) = average w s f + average w s g := by
  induction s using Finset.strongInduction generalizing f g with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [average_step w s _ hs, average_step w s f hs, average_step w s g hs,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih _ (Finset.erase_ssubset hx)]
      ring
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs, average_empty]

theorem average_mul (w : Nat → ℝ) (s : Finset Nat) (c : ℝ) (f : List Nat → ℝ) :
    average w s (fun xs => c * f xs) = c * average w s f := by
  induction s using Finset.strongInduction generalizing f with
  | H s ih =>
    by_cases hs : s.Nonempty
    · rw [average_step w s _ hs, average_step w s f hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [ih _ (Finset.erase_ssubset hx)]
      ring
    · simp [Finset.not_nonempty_iff_eq_empty.mp hs, average_empty]

theorem average_sub (w : Nat → ℝ) (s : Finset Nat) (f g : List Nat → ℝ) :
    average w s (fun xs => f xs - g xs) = average w s f - average w s g := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    (average_add w s f (fun xs => (-1 : ℝ) * g xs)).trans
      (congrArg (fun z => average w s f + z) (average_mul w s (-1) g))

theorem average_zero (w : Nat → ℝ) (s : Finset Nat) : average w s (fun _ => 0) = 0 := by
  simpa only [zero_mul] using average_mul w s 0 (fun _ => 0)

theorem average_sum (w : Nat → ℝ) (s u : Finset Nat) (f : Nat → List Nat → ℝ) :
    average w s (fun xs => ∑ a ∈ u, f a xs) = ∑ a ∈ u, average w s (f a) := by
  induction u using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, average_zero]
  | @insert a u ha ih =>
    simp only [Finset.sum_insert ha, average_add, ih]

end RotationBST.Treap.Random
