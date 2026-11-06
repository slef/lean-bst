module

public import RotationBST.Algorithms.GreedyASS.Combination.Policy
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination

private theorem minimum_allowance (a b A B allowance : ℝ)
    (left : a ≤ A + allowance) (right : b ≤ B) (nonneg : 0 ≤ allowance) :
    min a b ≤ min A B + allowance := by
  by_cases order : A ≤ B
  · rw [min_eq_left order]
    exact (min_le_left a b).trans left
  · rw [min_eq_right (le_of_not_ge order)]
    have selected := (min_le_right a b).trans right
    linarith

/-- One already fixed physical policy has both the optimized weighted-finger
and offline-competitive bounds. The shared startup allowance is linear;
the logarithmic worst-case transformation is supplied by the deamortized interface. -/
theorem Policy.weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) :
    (p.cost xs : ℝ) ≤ 1307904 * min
        (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
      3839872 * overhead saved := by
  have valid : ∀ x ∈ xs, x < saved.size := by
    rw [← size]
    exact AccessBridge.execution_valid execution
  have cost := (p.optimal_bound xs valid).2
  have lazy := (LazyFinger.Results.characterization_root saved.size start xs key valid).2
  have offline := Wilber.Results.rotation_lower_bound (Tango.balanced saved.size)
    ((Tango.balanced_size saved.size).trans size.symm) execution
  have left : (46225920 : ℝ) * LazyFinger.optimalCost saved.size xs ≤
      184903680 * WeightedFinger.optimalCostFrom saved.size start xs + 46225920 * saved.size := by nlinarith
  have right : (Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : ℝ) *
      (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat) ≤
      (4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat) := by
    have compared : Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
        (xs.length + Wilber.interleave (Tango.balanced saved.size) xs) ≤
        4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) * (xs.length + k) := by nlinarith
    exact_mod_cast compared
  have allowance : (46225920 : ℝ) * saved.size ≤ overhead saved := by
    simp only [overhead, Nat.cast_mul, Nat.cast_ofNat, le_refl]
  have minimum := minimum_allowance _ _ _ _ _ left right (by positivity)
  nlinarith

/-- The optimized statement implies the same minimum bound for every positive
weight assignment, without changing the prepared policy or its execution. -/
theorem Policy.weights_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (start : Nat) (key : start < saved.size)
    (w : Nat → ℝ) (positive : ∀ x < saved.size, 0 < w x)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) :
    (p.cost xs : ℝ) ≤ 1307904 * min
        (184903680 * WeightedFinger.costFrom w start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
      3839872 * overhead saved := by
  have valid : ∀ x ∈ xs, x < saved.size := by
    rw [← size]
    exact AccessBridge.execution_valid execution
  apply (p.weighted_competitive start key size execution).trans
  gcongr
  exact WeightedFinger.Results.optimal_le w saved.size start xs positive key valid

end RotationBST.Geometric.GreedyASS.Combination
