module

public import RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.ConditionalEntropy

/-- Grouping transition charges by their directed frequencies is exact. -/
theorem transitionSum_frequencies (n p : Nat) (xs : List Nat) (charge : Nat → Nat → ℝ)
    (initial : p < n) (valid : ∀ x ∈ xs, x < n) :
    transitionSum charge p xs = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
      (LazyFinger.frequency p xs a b : ℝ) * charge a b := by
  induction xs generalizing p with
  | nil => simp [transitionSum, LazyFinger.frequency]
  | cons x xs ih =>
    have first := valid x (by simp)
    have rest : ∀ y ∈ xs, y < n := fun y hy => valid y (by simp [hy])
    rw [transitionSum, ih x first rest]
    simp [LazyFinger.frequency, Nat.cast_add, add_mul, Finset.sum_add_distrib,
      ite_and, ite_mul, Finset.sum_ite_irrel, initial, first]

/-- With empirical frequencies, the information quantity is exactly the sum of
the per-transition logarithmic inverse probabilities used in query analysis. -/
theorem sequenceInformation_transitions (n p : Nat) (xs : List Nat)
    (initial : p < n) (valid : ∀ x ∈ xs, x < n) :
    transitionSum (fun a b => Real.logb 2
      ((rowTotal n (LazyFinger.frequency p xs) a : ℝ) / LazyFinger.frequency p xs a b)) p xs =
      sequenceInformation n p xs :=
  transitionSum_frequencies n p xs _ initial valid

end RotationBST.ConditionalEntropy
