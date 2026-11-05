module

public import RotationBST.Bounds.ConditionalEntropy.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.ConditionalEntropy

/-- Each finite row total dominates its entries, making every information term
nonnegative. Zero entries are handled without a positive-frequency assumption. -/
theorem information_nonneg (n : Nat) (f : Nat → Nat → Nat) : 0 ≤ information n f := by
  unfold information
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b hb
  by_cases zero : f a b = 0
  · simp [zero]
  · have positive : (0 : ℝ) < f a b := by exact_mod_cast Nat.pos_of_ne_zero zero
    have total : f a b ≤ rowTotal n f a := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb
    have ratio : (1 : ℝ) ≤ (rowTotal n f a : ℝ) / f a b := by
      apply (le_div_iff₀ positive).mpr
      simpa only [one_mul] using (show (f a b : ℝ) ≤ rowTotal n f a by exact_mod_cast total)
    exact mul_nonneg (le_of_lt positive) (Real.logb_nonneg (by norm_num) ratio)

theorem length_le_cost (n p : Nat) (xs : List Nat) : (xs.length : ℝ) ≤ cost n p xs := by
  have positive := information_nonneg n (LazyFinger.frequency p xs)
  change _ ≤ (xs.length : ℝ) + information n (LazyFinger.frequency p xs)
  linarith

/-- Exact conversion between total normalized information and average entropy,
including the empty sequence. -/
theorem cost_eq_length_mul_entropy (n p : Nat) (xs : List Nat) :
    cost n p xs = (xs.length : ℝ) * (1 + entropy n p xs) := by
  by_cases empty : xs = []
  · subst xs
    simp [cost, sequenceInformation, information, LazyFinger.frequency]
  · have lengthNonzero : xs.length ≠ 0 := fun h => empty (List.length_eq_zero_iff.mp h)
    have nonzero : (xs.length : ℝ) ≠ 0 := by exact_mod_cast lengthNonzero
    unfold cost entropy
    field_simp

end RotationBST.ConditionalEntropy
