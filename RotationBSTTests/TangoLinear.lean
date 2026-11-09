module

public import RotationBST.Algorithms.Tango.Algorithm.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TangoLinear
open Tango.Algorithm

-- On one key the doubly logarithmic factor vanishes: cost ≤ 20 (R + m) + 44.
example : ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
    start.size = 1 → Execution start xs finish offline →
      (A.totalCost start xs : ℝ) ≤ 20 * (offline + xs.length : Nat) + 44 := by
  obtain ⟨A, h⟩ := Results.exists_competitive_linear 1
  refine ⟨A, fun size execution => ?_⟩
  have := h size execution
  simpa [show Nat.log2 1 = 0 by decide] using this

-- The linear-startup algorithm is chosen before the comparator: the same `A`
-- bounds two different executions from two different initial trees.
example (n : Nat) {s₁ s₂ f₁ f₂ : Tree} {xs₁ xs₂ : List Nat} {r₁ r₂ : Nat}
    (h₁ : s₁.size = n) (e₁ : Execution s₁ xs₁ f₁ r₁)
    (h₂ : s₂.size = n) (e₂ : Execution s₂ xs₂ f₂ r₂) :
    ∃ A : Algorithm,
      (A.totalCost s₁ xs₁ : ℝ) ≤
          (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (r₁ + xs₁.length : Nat) + 44 * n ∧
      (A.totalCost s₂ xs₂ : ℝ) ≤
          (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (r₂ + xs₂.length : Nat) + 44 * n := by
  obtain ⟨A, h⟩ := Results.exists_competitive_linear n
  exact ⟨A, h h₁ e₁, h h₂ e₂⟩

end RotationBST.Tests.TangoLinear
