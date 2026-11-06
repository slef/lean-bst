module

public import RotationBST.Structures.PopTart.Chocolate.Pop.Fringe
public import RotationBST.Structures.PopTart.Chocolate.Population
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

/-- Borrowing releases the current singleton layer's credit; thawing restores
credits already retained in the frozen representation. -/
theorem pop_amortized {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    stack.popCost + rest.potential ≤ 20 + stack.potential := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => cases popped
    | one a =>
      rw [pop_last] at popped
      cases thawed : icing.thaw with
      | none => simp only [thawed, Option.map_none] at popped; cases popped
      | some next =>
        simp only [thawed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        rw [thaw_potential thawed]
        have cost : icing.popCost ≤ 6 := by cases icing <;> simp [Icing.popCost]
        simp only [Layer.popCost, Layer.potential, Regulars.potential]
        omega
    | two a b => cases popped; simp [Layer.popCost, Layer.potential, Regulars.potential]
    | three a b c => cases popped; simp [Layer.popCost, Layer.potential, Regulars.potential]; omega
  | next rs child icing =>
    cases rs with
    | zero => cases popped
    | one a =>
      rw [pop_next] at popped
      cases base : child.baseCrumb with
      | some block =>
        cases block with
        | leaf => simp only [base] at popped; cases popped
        | node b c =>
          simp only [base, Option.some.injEq, Prod.mk.injEq] at popped
          rcases popped with ⟨rfl, rfl⟩
          rw [popCost_next, base]
          have same := base_eq base
          subst child
          simp [Layer.potential, Regulars.potential, Icing.potential]
          omega
      | none =>
        cases result : child.pop with
        | none => simp only [base, result] at popped; cases popped
        | some pair =>
          rcases pair with ⟨block, suffix⟩
          cases block with
          | leaf => simp only [base, result] at popped; cases popped
          | node b c =>
            simp only [base, result, Option.some.injEq, Prod.mk.injEq] at popped
            rcases popped with ⟨rfl, rfl⟩
            have bound := pop_amortized result
            rw [popCost_next, base]
            simp only [Layer.potential, Regulars.potential]
            omega
    | two a b => cases popped; simp [Layer.popCost, Layer.potential, Regulars.potential]; omega
    | three a b c => cases popped; simp [Layer.popCost, Layer.potential, Regulars.potential]; omega
termination_by stack

theorem pop_cost_active_depth (stack : Layer) : stack.popCost ≤ 10 * stack.activeDepth + 6 := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => simp [Layer.popCost, Layer.activeDepth]
    | one a => cases icing <;> simp [Layer.popCost, Icing.popCost, Layer.activeDepth]
    | two a b => simp [Layer.popCost, Layer.activeDepth]
    | three a b c => simp [Layer.popCost, Layer.activeDepth]
  | next rs child icing =>
    have bound := pop_cost_active_depth child
    cases rs with
    | zero => simp [Layer.popCost, Layer.activeDepth]
    | one a =>
      rw [popCost_next]
      cases child.baseCrumb <;> simp only [Layer.activeDepth] <;> omega
    | two a b => simp [Layer.popCost, Layer.activeDepth]
    | three a b c => simp [Layer.popCost, Layer.activeDepth]
termination_by stack

/-- A pop, including one operation unit, has logarithmic worst-case cost in
the number of original fringe leaves, independently of their weights. -/
theorem pop_worst_case {stack : Layer} (valid : stack.Valid 0) :
    (1 + stack.popCost : ℝ) ≤ 7 + 10 * Real.logb 2 (stack.decode.leafCount) := by
  have population : 2 ^ stack.activeDepth ≤ stack.decode.leafCount := by
    simpa only [Nat.zero_add] using active_population valid
  have realPopulation : (2 : ℝ) ^ stack.activeDepth ≤ (stack.decode.leafCount : ℝ) := by exact_mod_cast population
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) realPopulation
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at logarithm
  have cost : (stack.popCost : ℝ) ≤ 10 * (stack.activeDepth : ℝ) + 6 := by
    exact_mod_cast pop_cost_active_depth stack
  linarith only [cost, logarithm]

end RotationBST.PopTart.Chocolate
