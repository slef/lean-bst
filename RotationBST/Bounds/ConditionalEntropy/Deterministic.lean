module

public import RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.ConditionalEntropy

/-- A deterministic successor rule permits at most one nonzero entry per row. -/
theorem frequency_off_successor (next : Nat → Nat) (p : Nat) (xs : List Nat)
    (follows : Follows next p xs) (a b : Nat) (different : b ≠ next a) :
    LazyFinger.frequency p xs a b = 0 := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    have first : ¬ (a = p ∧ b = x) := by
      rintro ⟨rfl, rfl⟩
      exact different follows.1.symm
    simp only [LazyFinger.frequency, first, ↓reduceIte, Nat.zero_add]
    exact ih x follows.2

/-- A transition matrix with at most one possible successor per key has zero
conditional information, regardless of how unequal the row frequencies are. -/
theorem information_deterministic (n : Nat) (f : Nat → Nat → Nat) (next : Nat → Nat)
    (deterministic : ∀ a b, b ≠ next a → f a b = 0) : information n f = 0 := by
  unfold information
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b hb
  by_cases zero : f a b = 0
  · simp [zero]
  · have successor : b = next a := by
      by_contra different
      exact zero (deterministic a b different)
    have total : rowTotal n f a = f a b := by
      unfold rowTotal
      apply Finset.sum_eq_single b
      · intro c _ different
        exact deterministic a c (by simpa only [← successor] using different)
      · intro missing
        exact False.elim (missing hb)
    rw [total]
    have positive : (f a b : ℝ) ≠ 0 := by exact_mod_cast zero
    simp [div_self positive]

theorem sequenceInformation_follows (n p : Nat) (xs : List Nat) (next : Nat → Nat)
    (follows : Follows next p xs) : sequenceInformation n p xs = 0 :=
  information_deterministic n _ next (frequency_off_successor next p xs follows)

theorem adjacentInformation_follows (n p : Nat) (xs : List Nat) (next : Nat → Nat)
    (follows : Follows next p xs) : adjacentInformation n xs = 0 := by
  cases xs with
  | nil => rfl
  | cons x xs => exact sequenceInformation_follows n x xs next follows.2

theorem follows_append (next : Nat → Nat) (p : Nat) (xs ys : List Nat)
    (first : Follows next p xs) (last : Follows next (xs.getLastD p) ys) :
    Follows next p (xs ++ ys) := by
  induction xs generalizing p with
  | nil => exact last
  | cons x xs ih =>
    exact ⟨first.1, ih x first.2 (by simpa only [List.getLastD_cons] using last)⟩

theorem follows_repeat (next : Nat → Nat) (p : Nat) (period : List Nat)
    (one : Follows next p period) (closed : period.getLastD p = p) (rounds : Nat) :
    Follows next p (repeatPeriod period rounds) := by
  induction rounds with
  | zero => trivial
  | succ rounds ih => exact follows_append next p period _ one (by simpa only [closed] using ih)

@[simp] theorem repeat_length (period : List Nat) (rounds : Nat) :
    (repeatPeriod period rounds).length = rounds * period.length := by
  induction rounds with
  | zero => simp [repeatPeriod]
  | succ rounds ih => simp only [repeatPeriod, List.length_append, ih]; ring

theorem repeat_valid (n : Nat) (period : List Nat) (valid : ∀ x ∈ period, x < n) (rounds : Nat) :
    ∀ x ∈ repeatPeriod period rounds, x < n := by
  induction rounds with
  | zero => simp [repeatPeriod]
  | succ rounds ih => intro x hx; exact (List.mem_append.mp hx).elim (valid x) (ih x)

end RotationBST.ConditionalEntropy
