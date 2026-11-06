module

public import RotationBST.Structures.PopTart.Chocolate.Pop.Traces
public import RotationBST.Structures.PopTart.Chocolate.Pop.Accounting
public import RotationBST.Structures.PopTart.Chocolate.Weighted
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

theorem operation_valid {level : Nat} {stack rest : Layer} (valid : stack.Valid level)
    (op : Operation level stack rest) : rest.Valid level := by
  cases op with
  | push new perfect nonnegative => exact push_valid valid perfect nonnegative
  | pop rest crumb popped => exact (popped_valid valid popped).2.2

theorem operation_trace {level : Nat} {stack rest : Layer} (op : Operation level stack rest)
    (cs : List Pointer.Frame) : Pointer.Trace ⟨op.input, cs⟩ ⟨op.output, cs⟩ op.cost := by
  cases op with
  | push new perfect nonnegative => exact (push_trace stack new).under cs
  | pop rest crumb popped => exact (pop_trace popped).under cs

theorem operation_amortized {level : Nat} {stack rest : Layer} (op : Operation level stack rest) :
    op.cost + rest.potential ≤ 20 + stack.potential := by
  cases op with
  | push new perfect nonnegative => exact push_amortized stack new
  | pop rest crumb popped => exact pop_amortized popped

/-- Both operations have logarithmic worst-case cost in the current leaf
population, independently of weight order or magnitude. -/
theorem operation_worst_case {stack rest : Layer} (valid : stack.Valid 0)
    (op : Operation 0 stack rest) :
    (1 + op.cost : ℝ) ≤ 7 + 14 * Real.logb 2 stack.decode.leafCount := by
  cases op with
  | push new perfect nonnegative => exact push_worst_case valid
  | pop rest crumb popped =>
    have bound := pop_worst_case valid
    have population := active_population valid
    simp only [Nat.zero_add] at population
    have minimum := Nat.one_le_pow stack.activeDepth 2 (by decide)
    have count : (1 : ℝ) ≤ (stack.decode.leafCount : ℝ) := by
      exact_mod_cast minimum.trans population
    have logarithm := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) count
    change (1 + stack.popCost : ℝ) ≤ 7 + 14 * Real.logb 2 stack.decode.leafCount
    linarith only [bound, logarithm]

/-- Arbitrary mixed histories preserve validity and realize every actual
operation boundary, with one potential telescoping across pushes and pops. -/
theorem sequence {level : Nat} {stack rest : Layer} {n : Nat}
    (program : Program level stack rest n) (valid : stack.Valid level) :
    rest.Valid level ∧ program.Realizes ∧ program.cost + rest.potential ≤ 20 * n + stack.potential := by
  induction program with
  | nil stack => exact ⟨valid, .nil stack, by simp [Program.cost]⟩
  | @cons stack middle rest n op tail ih =>
    obtain ⟨validRest, realized, bound⟩ := ih (operation_valid valid op)
    have first := operation_amortized op
    exact ⟨validRest, .cons (operation_trace op []) realized, by simp only [Program.cost]; omega⟩

theorem empty_sequence {level : Nat} {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Program level (.last .zero (.base bottom)) rest n)
    (base : Perfect level bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid level ∧ program.Realizes ∧ n + program.cost ≤ 21 * n := by
  have initial : (Layer.last .zero (.base bottom)).Valid level :=
    ⟨trivial, ⟨base, nonnegative⟩, fun _ => ⟨bottom, rfl⟩⟩
  obtain ⟨valid, realized, bound⟩ := sequence program initial
  exact ⟨valid, realized, by simp only [Layer.potential, Icing.potential, Regulars.potential] at bound; omega⟩

/-- Lemma 4's arbitrary-weight mixed-history guarantee: constant amortized
operation cost together with weighted depth for every final occurrence. -/
theorem weighted_sequence {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Program 0 (.last .zero (.base bottom)) rest n)
    (base : Perfect 0 bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid 0 ∧ program.Realizes ∧ n + program.cost ≤ 21 * n ∧
      ∀ subtree weight depth, SlotAt rest.decode subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (rest.decode.mass / weight) := by
  obtain ⟨valid, realizes, bound⟩ := empty_sequence program base nonnegative
  exact ⟨valid, realizes, bound, fun _ _ _ slot positive => weighted_depth valid slot positive⟩

end RotationBST.PopTart.Chocolate
