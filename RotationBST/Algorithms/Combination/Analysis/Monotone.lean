module

public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- Increasing a common initialization allowance preserves the complete
contract, including segment stability. The multiplier must cover one copy of
that allowance; no request charges or worker choices are changed. -/
theorem WellBehaved.overhead_mono {σ : Type} {worker : Controller.Worker σ}
    {n overhead larger C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges)
    (increased : overhead ≤ larger) (constant : 1 ≤ C₁) :
    WellBehaved worker n larger C₀ C₁ charges := by
  refine ⟨well.nonneg, ?_, ?_, ?_⟩
  · intro side earlier state spent ran valid x key
    obtain ⟨final, cost, served, bound⟩ := well.single side earlier state spent ran valid x key
    exact ⟨final, cost, served, bound.trans (Nat.mul_le_mul_left _ increased)⟩
  · intro side xs valid
    obtain ⟨final, cost, ran, bound⟩ := well.upper side xs valid
    have growth : (overhead : ℝ) ≤ larger := by exact_mod_cast increased
    exact ⟨final, cost, ran, by linarith⟩
  · intro side xs valid lo hi ordered inside
    have bound := well.stable side xs valid lo hi ordered inside
    have growth : (overhead : ℝ) ≤ larger := by exact_mod_cast increased
    have multiplier : (1 : ℝ) ≤ C₁ := by exact_mod_cast constant
    have paid := mul_nonneg (sub_nonneg.mpr multiplier) (sub_nonneg.mpr growth)
    nlinarith

end RotationBST.Combo.Analysis
