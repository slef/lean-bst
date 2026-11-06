module

public import RotationBST.Algorithms.Combination.Analysis.Amortized

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- The comparator is selected only in the proof. The same causal controller
has the bound for the smaller of the two original-sequence charge totals. -/
theorem minimum_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * min (total charges false xs) (total charges true xs) + 3 * overhead) := by
  by_cases better : total charges false xs ≤ total charges true xs
  · simpa only [min_eq_left better] using prefix_bound well valid execution false
  · simpa only [min_eq_right (le_of_not_ge better)] using prefix_bound well valid execution true

/-- A single fixed executable controller completes every valid input prefix
and satisfies the two-worker comparison, under the stated operational
well-behaved bounds and explicit restore charge. -/
theorem execute {σ : Type} (worker : Controller.Worker σ) (n overhead C₀ C₁ restoreFactor : Nat) (charges : Charges)
    (well : WellBehaved worker n overhead C₀ C₁ charges) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ final cost switches,
      Controller.run worker (budget overhead C₁) (restoreFactor * overhead)
        (Controller.initial worker (budget overhead C₁)) xs = some (final, cost) ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        (Controller.initial worker (budget overhead C₁)) xs final cost switches ∧
      (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * min (total charges false xs) (total charges true xs) + 3 * overhead) := by
  have enough : C₁ * overhead ≤ budget overhead C₁ := by simp only [budget, Nat.add_mul, Nat.one_mul]; omega
  obtain ⟨final, cost, switches, execution, computed, _, _⟩ :=
    Controller.complete worker n (C₁ * overhead) (budget overhead C₁) (restoreFactor * overhead)
      well.fresh enough (Controller.initial worker (budget overhead C₁)) (by simp [Controller.initial]) xs valid
  exact ⟨final, cost, switches, computed, execution, minimum_bound well valid execution⟩

end RotationBST.Combo.Analysis
