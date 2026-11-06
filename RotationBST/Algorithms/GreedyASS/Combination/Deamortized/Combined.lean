module

public import RotationBST.Algorithms.GreedyASS.Combination.Deamortized.Policy
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination

/-- The normalized weighted-finger/competitive minimum has an explicit linear
startup allowance. Its competitive coefficient grows doubly logarithmically. -/
theorem Deamortized.linear_weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds}
    {oldData : Nat → Nat} {p : Policy saved fields oldData} (d : Deamortized p)
    (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((8 * ⌈64 * (14 * Real.logb 2 (Nat.log2 saved.size + 1) + 6)⌉₊ : Nat) * (xs.length + k : Nat)) +
        3839872 * (46225920 * saved.size : Nat)) := by
  have bound := d.weighted_competitive start key size execution completed
  have factor := Tango.Combination.Results.balanced_linear_factor saved.size
  have multiplied : 4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) ≤
      8 * ⌈64 * (14 * Real.logb 2 (Nat.log2 saved.size + 1) + 6)⌉₊ := by omega
  apply bound.trans
  simp only [overhead]
  gcongr

/-- One causal BST program simultaneously has linear startup, optimized
weighted finger, doubly logarithmic competitiveness, and logarithmic worst-case
responses. This is the abstract BST-operation form of Theorem 4.3; private
computation and finite-word storage bounds are separate obligations. -/
theorem combined (saved : Tree) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Policy saved fields oldData, ∃ d : Deamortized p,
      ∀ xs : List Nat, (∀ x ∈ xs, x < saved.size) →
        ∃ out, d.program xs = some out ∧
          Deamortization.Scheduler.ServedStream ⟨d.initial, []⟩ xs out.state.cursor out.instructions out.costs ∧
          out.costs.length = xs.length ∧ out.costs.sum = xs.length + out.instructions.length ∧
          (∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size) ∧
          ∀ (start : Nat), start < saved.size → ∀ (s t : Tree) (k : Nat), s.size = saved.size →
            RotationBST.Execution s xs t k →
              (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
                (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
                  ((8 * ⌈64 * (14 * Real.logb 2 (Nat.log2 saved.size + 1) + 6)⌉₊ : Nat) * (xs.length + k : Nat)) +
                  3839872 * (46225920 * saved.size : Nat)) := by
  obtain ⟨p⟩ := policy_exists saved nonempty fields oldData
  obtain ⟨d⟩ := deamortized_exists p nonempty
  refine ⟨p, d, ?_⟩
  intro xs valid
  obtain ⟨out, completed, _replay, served, _execution, length, total, _bound, worst⟩ := d.correct xs valid
  refine ⟨out, completed, served, length, total, worst, ?_⟩
  intro start key s t k size execution
  exact d.linear_weighted_competitive start key size execution completed

end RotationBST.Geometric.GreedyASS.Combination
