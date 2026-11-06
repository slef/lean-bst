module

public import RotationBST.Algorithms.Combination.Analysis.Windows
public import RotationBST.Algorithms.Combination.Controller.Intervals

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- Every contiguous interval of the same executed input has the minimum
comparison. Its work is the actual middle summand of that execution, with
the original boundary states and the original input's amortized charges. -/
theorem executed_window {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead) s xs t cost switches)
    (lo hi : Nat) (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    ∃ beforeState afterState beforeCost windowCost afterCost beforeSwitches windowSwitches afterSwitches,
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        s (xs.take lo) beforeState beforeCost beforeSwitches ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        beforeState (segment xs lo hi) afterState windowCost windowSwitches ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        afterState (xs.drop hi) t afterCost afterSwitches ∧
      cost = beforeCost + windowCost + afterCost ∧ switches = beforeSwitches + windowSwitches + afterSwitches ∧
      (windowCost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * C₀ * min (mass charges false xs lo hi) (mass charges true xs lo hi) + (2 * C₀ * C₁ + 5) * overhead) := by
  obtain ⟨beforeState, afterState, beforeCost, windowCost, afterCost, beforeSwitches, windowSwitches, afterSwitches,
    first, middle, last, work, changed⟩ := execution.window ordered
  exact ⟨beforeState, afterState, beforeCost, windowCost, afterCost, beforeSwitches, windowSwitches, afterSwitches,
    first, middle, last, work, changed, window_minimum well (first.left_le limit) valid ordered inside middle⟩

end RotationBST.Combo.Analysis
