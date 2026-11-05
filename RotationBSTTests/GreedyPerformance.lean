module

public import RotationBST.Algorithms.GreedyASS.Performance.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.GreedyPerformance
open Geometric Geometric.GreedyASS Geometric.GreedyASS.Reference

private def one : Tree := .node .nil .nil
private def three : Tree := .node one one
private def seven : Tree := .node three three
private def heavy (x : Nat) : ℝ := if x = 1 then 100 else 1

-- Empty children are contracted in all four node cases. Leaves preserve
-- the original rank interval, including a nonzero reference offset.
example : Conversion.convert one = .nil ∧
    Conversion.convert (.node one .nil) = .node .nil .nil ∧
    Conversion.convert (.node .nil one) = .node .nil .nil ∧
    Conversion.convert three = .node .nil (.node .nil .nil) ∧
    leaves (Conversion.convert seven) = 7 := by decide
example : leaves (Conversion.convert seven) = seven.size :=
  Conversion.Results.population seven (by decide)
example : Distance.depth (Conversion.convert seven) 10 13 ≤ 2 * Tree.depth seven 3 + 2 :=
  Conversion.Results.depth seven 10 3 (by decide)

-- Endpoint gadgets matter: the original parent/child distance is one,
-- while the represented leaves are five edges apart. The proved bridge
-- includes this overhead and does not assume a factor two on raw edges.
example : LazyFinger.distance seven 3 1 = 1 ∧
    Transitions.edges (Conversion.convert seven) 0 3 1 = 5 ∧
    Transitions.edges (Conversion.convert seven) 10 13 11 = 5 ∧
    Transitions.edges (Conversion.convert seven) 0 3 3 = 0 := by decide
example : Transitions.edges (Conversion.convert seven) 10 13 11 ≤
    2 * LazyFinger.distance seven 3 1 + 4 :=
  Conversion.Results.distance seven 10 3 1 (by decide) (by decide)
example : Potential.Amortized.referenceCost (Conversion.convert seven) 0 [3, 1, 3, 3] ≤
    5 * LazyFinger.costFrom seven 6 [3, 1, 3, 3] :=
  Conversion.Results.cost_from seven 6 [3, 1, 3, 3] (by decide) (by decide)

-- Ordinary-tree costs cover an empty key universe and a non-root initial
-- finger. No dummy leaf is charged for the empty universe.
example : rowCost greedySweep 0 ∅ [] ≤ 120 * LazyFinger.cost .nil [] + 15 * Tree.size .nil :=
  Performance.Results.lazy_tree .nil [] (by simp)
example : rowCost greedySweep 0 ∅ [] ≤ 120 * LazyFinger.optimalCost 0 [] := by
  simpa using Performance.Results.lazy_optimal 0 [] (by simp)
example : rowCost greedySweep 0 ∅ [3, 1, 3, 3] ≤
    120 * LazyFinger.costFrom seven 6 [3, 1, 3, 3] + 15 * 7 :=
  Performance.Results.lazy_from seven 6 [3, 1, 3, 3] (by decide) (by decide)

-- Repeated searches retain a unit charge even with nonuniform weights.
example : WeightedFinger.costFrom heavy 1 [1, 1, 1] = 3 := by
  have selfCharge := WeightedFinger.Results.repeated_key heavy 1 (by norm_num [heavy])
  norm_num [WeightedFinger.costFrom, selfCharge]
example : (rowCost greedySweep 0 ∅ [1, 1, 1] : ℝ) ≤
    480 * WeightedFinger.costFrom heavy 1 [1, 1, 1] + 15 * 3 :=
  Performance.Results.weighted heavy 3 1 [1, 1, 1]
    (by intro k _; unfold heavy; split <;> norm_num) (by decide) (by decide)
example : (rowCost greedySweep 0 ∅ [0, 2, 1, 0] : ℝ) ≤
    480 * Bounds.dynamicFingerCostFrom 2 [0, 2, 1, 0] + 15 * 3 :=
  Performance.Results.dynamic 3 2 [0, 2, 1, 0] (by decide) (by decide)

-- The chosen policy handles both weightings for every stream and initial
-- tree. Neither the weights nor the benchmark predecessor select a policy.
example : ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = 3 →
    ∀ xs : List Nat, (∀ x ∈ xs, x < 3) →
      (algorithm.totalCost initial xs : ℝ) ≤
        2889120 * WeightedFinger.costFrom heavy 1 xs + 96303 * 3 ∧
      (algorithm.totalCost initial xs : ℝ) ≤
        2889120 * Bounds.dynamicFingerCostFrom 2 xs + 96303 * 3 := by
  obtain ⟨algorithm, bound⟩ := Performance.Results.bst_weighted 3
  refine ⟨algorithm, ?_⟩
  intro initial size xs valid
  constructor
  · exact bound initial size 1 (by decide) heavy
      (by intro k _; unfold heavy; split <;> norm_num) xs valid
  · simpa only [LazyFinger.Consequences.Results.unit_weights, Nat.cast_ofNat] using
      bound initial size 2 (by decide) (fun _ => 1) (by intros; norm_num) xs valid

end RotationBST.Tests.GreedyPerformance
