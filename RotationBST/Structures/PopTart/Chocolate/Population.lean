module

public import RotationBST.Structures.PopTart.Chocolate.Regulars
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

private theorem attach_count (rs : Regulars) (tail : WeightedTree) :
    tail.leafCount ≤ (rs.attach tail).leafCount := by
  cases rs <;> simp only [Regulars.attach, leafCount] <;> omega

/-- The bottom crumb of an icing retains at least the population of its level,
regardless of how many blocks have been frozen above it. -/
theorem icing_population {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    2 ^ level ≤ icing.decode.leafCount := by
  cases icing with
  | base crumb => exact le_of_eq (perfect_count valid.1).symm
  | solid crumb tail =>
    have bound := icing_population valid.2.2.1
    change 2 ^ level ≤ crumb.leafCount + tail.decode.leafCount
    omega
  | frozen carry old tail =>
    have bound := icing_population valid.2.2.2.1
    change 2 ^ level ≤ carry.leafCount + old.decode.leafCount + tail.decode.leafCount
    omega
termination_by icing

/-- Every active next-layer transition doubles the minimum crumb population.
This controls carry length independently of all weight magnitudes. -/
theorem active_population {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    2 ^ (level + stack.activeDepth) ≤ stack.decode.leafCount := by
  cases stack with
  | last rs icing =>
    have bound := icing_population valid.2.1
    exact bound.trans (attach_count rs icing.decode)
  | next rs child icing =>
    have bound := active_population valid.2.1
    have count := attach_count rs (.node child.decode icing.decode)
    simp only [Layer.activeDepth]
    rw [show level + (child.activeDepth + 1) = level + 1 + child.activeDepth by omega]
    change child.decode.leafCount + icing.decode.leafCount ≤ (Layer.next rs child icing).decode.leafCount at count
    omega
termination_by stack

theorem push_cost_active_depth (stack : Layer) : stack.pushCost ≤ 14 * stack.activeDepth + 6 := by
  classical
  cases stack with
  | last rs icing => cases rs <;> simp [Layer.pushCost, Layer.activeDepth]
  | next rs child icing =>
    have bound := push_cost_active_depth child
    cases rs with
    | zero => simp [Layer.pushCost, Layer.activeDepth]
    | one a => simp [Layer.pushCost, Layer.activeDepth]
    | two a b => simp [Layer.pushCost, Layer.activeDepth]
    | three a b c =>
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · simp only [Layer.pushCost, thin, ite_true, Layer.activeDepth]
        omega
      · simp only [Layer.pushCost, thin, ite_false, Layer.activeDepth]
        omega
termination_by stack

/-- One unit for the push itself plus all rebalancing is logarithmic in the
number of original fringe leaves, even with arbitrarily skewed weights. -/
theorem push_worst_case {stack : Layer} (valid : stack.Valid 0) :
    (1 + stack.pushCost : ℝ) ≤ 7 + 14 * Real.logb 2 (stack.decode.leafCount) := by
  have population : 2 ^ stack.activeDepth ≤ stack.decode.leafCount := by
    simpa only [Nat.zero_add] using active_population valid
  have realPopulation : (2 : ℝ) ^ stack.activeDepth ≤ (stack.decode.leafCount : ℝ) := by exact_mod_cast population
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) realPopulation
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at logarithm
  have cost : (stack.pushCost : ℝ) ≤ 14 * (stack.activeDepth : ℝ) + 6 := by
    exact_mod_cast push_cost_active_depth stack
  linarith only [cost, logarithm]

end RotationBST.PopTart.Chocolate
