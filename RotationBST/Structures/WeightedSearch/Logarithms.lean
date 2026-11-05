module

public import RotationBST.Structures.WeightedSearch.Construction
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedSearch

/-- Positive-frequency keys have logarithmic depth in the reciprocal of their
relative frequency. No height claim is made for zero-frequency keys. -/
theorem build_depth (weights : List Nat) (x : Nat) (valid : x < weights.length)
    (positive : 0 < weights[x]) :
    (Tree.depth (build weights) x : ℝ) ≤ Real.logb 2 ((weights.sum : ℝ) / weights[x]) := by
  have mass := build_mass weights x valid
  have weightPositive : (0 : ℝ) < weights[x] := by exact_mod_cast positive
  have ratio : (2 : ℝ) ^ Tree.depth (build weights) x ≤ (weights.sum : ℝ) / weights[x] := by
    apply (le_div_iff₀ weightPositive).mpr
    exact_mod_cast mass
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  simpa only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] using logarithm

end RotationBST.WeightedSearch
