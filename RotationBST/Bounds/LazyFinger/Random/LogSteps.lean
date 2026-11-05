module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger.RandomAnalysis

/-- A right-endpoint rectangle under the reciprocal function. -/
theorem ratio_step (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    b / (a + b) ≤ Real.log (a + b) - Real.log a := by
  have hab : 0 < a + b := by linarith
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hab ha)
  rw [Real.log_div hab.ne' ha.ne'] at h
  have he : 1 - ((a + b) / a)⁻¹ = b / (a + b) := by
    field_simp
    ring
  rwa [he] at h

/-- Keeping the difference of reciprocal terms permits a bound independent
of the total weight outside the query interval. -/
theorem difference_step (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    b / (a + b) - b / (a + b + c) ≤
      (Real.log (a + c) - Real.log a) -
        (Real.log (a + b + c) - Real.log (a + b)) := by
  have hab : 0 < a + b := by linarith
  have hac : 0 < a + c := by linarith
  have habc : 0 < a + b + c := by linarith
  have hp : 0 < (a + b) * (a + c) / (a * (a + b + c)) :=
    div_pos (mul_pos hab hac) (mul_pos ha habc)
  have hlog := Real.one_sub_inv_le_log_of_pos hp
  have he : 1 - ((a + b) * (a + c) / (a * (a + b + c)))⁻¹ =
      b * c / ((a + b) * (a + c)) := by
    field_simp
    ring
  rw [he] at hlog
  have hdiff : b / (a + b) - b / (a + b + c) =
      b * c / ((a + b) * (a + b + c)) := by
    field_simp
    ring
  rw [hdiff]
  have hrat : b * c / ((a + b) * (a + b + c)) ≤ b * c / ((a + b) * (a + c)) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hb hc) (mul_pos hab hac)
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hab)
  apply hrat.trans
  convert hlog using 1
  rw [Real.log_div (mul_pos hab hac).ne' (mul_pos ha habc).ne',
    Real.log_mul hab.ne' hac.ne', Real.log_mul ha.ne' habc.ne']
  ring

/-- Sum local potential increases over an integer interval. -/
theorem sum_le_rise (f g : Nat → ℝ) (lo hi : Nat) (h : lo ≤ hi)
    (step : ∀ i ∈ Finset.Ico lo hi, f i ≤ g (i + 1) - g i) :
    ∑ i ∈ Finset.Ico lo hi, f i ≤ g hi - g lo := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico lo hi, (g (i + 1) - g i) := Finset.sum_le_sum step
    _ = _ := Finset.sum_Ico_sub _ h

theorem sum_le_fall (f g : Nat → ℝ) (lo hi : Nat) (h : lo ≤ hi)
    (step : ∀ i ∈ Finset.Ico lo hi, f i ≤ g i - g (i + 1)) :
    ∑ i ∈ Finset.Ico lo hi, f i ≤ g lo - g hi := by
  have hh := sum_le_rise f (fun i => -g i) lo hi h (by
    intro i hi
    have := step i hi
    linarith)
  linarith

end RotationBST.LazyFinger.RandomAnalysis
