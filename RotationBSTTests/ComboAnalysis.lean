module

public import RotationBST.Algorithms.Combination.Analysis.Abstract
public import RotationBST.Algorithms.Combination.Rounds.Certificates.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboAnalysis
open Combo

private def worker : Controller.Worker Nat := ⟨fun _ => 0, fun _ _ _ => (0, true)⟩
private def charges : Analysis.Charges := fun side _ _ => if side then 2 else 1

private theorem requests (side : Bool) (xs : List Nat) : Worker.Requests worker side 0 xs 0 xs.length := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simpa only [List.length_cons, Nat.add_comm] using Worker.Requests.cons (Controller.AttemptRun.done (fuel := 0) rfl) ih

private theorem total_formula (side : Bool) (xs : List Nat) :
    Analysis.total charges side xs = (if side then 2 else 1 : ℝ) * xs.length := by
  cases side <;> simp [Analysis.total, Analysis.mass, charges, mul_comm]

-- A concrete nonvacuous instance: both workers take one unit per request,
-- while the two declared amortized charges are respectively one and two.
private theorem well (n : Nat) : Analysis.WellBehaved worker n 1 1 1 charges := by
  constructor
  · intro side xs i
    cases side <;> norm_num [charges]
  · intro side earlier state spent _ _ x _
    exact ⟨0, 1, Controller.AttemptRun.done (fuel := 0) rfl, by decide⟩
  · intro side xs _
    refine ⟨0, xs.length, requests side xs, ?_⟩
    rw [total_formula]
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    all_goals have nonneg : (0 : ℝ) ≤ xs.length := Nat.cast_nonneg _; linarith
  · intro side xs _ lo hi ordered inside
    have length : (Analysis.segment xs lo hi).length = hi - lo := by
      simp only [Analysis.segment, List.length_take, List.length_drop]
      omega
    rw [total_formula, length]
    cases side <;> simp [Analysis.mass, charges, mul_comm]

private def xs : List Nat := [0, 1, 2, 3, 4]
private theorem valid : ∀ x ∈ xs, x < 5 := by
  intro x member
  simp only [xs, List.mem_cons, List.not_mem_nil, or_false] at member
  omega

example : Controller.run worker (Analysis.budget 1 1) 3 (Controller.initial worker (Analysis.budget 1 1)) xs =
    some (⟨false, 0, 1⟩, 11) := by decide

example : ∃ final cost switches,
    Controller.run worker (Analysis.budget 1 1) (3 * 1) (Controller.initial worker (Analysis.budget 1 1)) xs = some (final, cost) ∧
    Controller.Execution worker (Analysis.budget 1 1) (3 * 1) (Controller.initial worker (Analysis.budget 1 1)) xs final cost switches ∧
    (cost : ℝ) ≤ (1 + 1 + 3 : Nat) *
      (2 * 1 * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * 1) :=
  by simpa only [Nat.cast_one] using Analysis.Results.execute worker 5 1 1 1 3 charges (well 5) xs valid

-- The actual cost is bounded by the minimum charge even though the
-- controller's transition rule never reads these charges.
private theorem execution : Controller.Execution worker 2 3 (Controller.initial worker 2) xs ⟨false, 0, 1⟩ 11 2 :=
  .cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) .nil))))

example : (11 : ℝ) ≤ 65 := by
  have trace : Controller.Execution worker (Analysis.budget 1 1) (3 * 1)
      (Controller.initial worker (Analysis.budget 1 1)) xs ⟨false, 0, 1⟩ 11 2 := by
    simpa only [Analysis.budget] using execution
  have bound := Analysis.Results.minimum_bound (restoreFactor := 3) (well 5) valid trace
  norm_num [total_formula, xs] at bound ⊢

-- Empty prefixes also have a completed execution; no closed-round division
-- by the overhead is used in the comparison theorem.
example : ∃ final cost switches,
    Controller.run worker (Analysis.budget 1 1) 0 (Controller.initial worker (Analysis.budget 1 1)) [] = some (final, cost) ∧
    Controller.Execution worker (Analysis.budget 1 1) 0 (Controller.initial worker (Analysis.budget 1 1)) [] final cost switches ∧
    (cost : ℝ) ≤ (1 + 1 + 0 : Nat) *
      (2 * 1 * min (Analysis.total charges false []) (Analysis.total charges true []) + 3 * 1) :=
  by simpa only [Nat.cast_one, Nat.zero_mul] using Analysis.Results.execute worker 0 1 1 1 0 charges (well 0) [] (by simp)

-- The window starts with an exhausted old round. Its first request is
-- charged for the retry and restore, and another switch occurs inside it.
private theorem windowExecution : Controller.Execution worker 2 3 ⟨false, 0, 0⟩ [2, 3, 4] ⟨false, 0, 1⟩ 9 2 :=
  .cons (by decide) (.cons (by decide) (.cons (by decide) .nil))

example : Controller.run worker 2 3 ⟨false, 0, 0⟩ (Analysis.segment xs 2 5) = some (⟨false, 0, 1⟩, 9) := by decide

-- Exactly the interior true-worker span has a full-budget certificate;
-- the first false-worker span starts with no budget and is excluded.
example : (Rounds.spans worker 2 3 ⟨false, 0, 0⟩ 0 [2, 3, 4]).dropLast.tail = [⟨true, 0, 3⟩] := by decide
example : Worker.ClosedRound worker true (worker.restart true) 2 [2, 3, 4] :=
  Rounds.Certificates.Results.interior_spans windowExecution ⟨true, 0, 3⟩ (by decide)

example : (9 : ℝ) ≤ 65 := by
  have trace : Controller.Execution worker (Analysis.budget 1 1) (3 * 1)
      ⟨false, 0, 0⟩ (Analysis.segment xs 2 5) ⟨false, 0, 1⟩ 9 2 := by
    simpa [Analysis.budget, Analysis.segment, xs] using windowExecution
  have bound := Analysis.Results.window_minimum (restoreFactor := 3) (well 5) (by decide) valid
    (by decide : 2 ≤ 5) (by decide : 5 ≤ xs.length) trace
  convert bound using 1; norm_num [Analysis.mass, charges]

-- The bounded window cost is the actual middle execution's cost and is
-- part of the original total 11, rather than the cost of a restarted run.
example : ∃ beforeState afterState windowCost,
    Controller.run worker 2 3 beforeState (Analysis.segment xs 2 5) = some (afterState, windowCost) ∧
    windowCost ≤ 11 ∧ (windowCost : ℝ) ≤ 65 := by
  have trace : Controller.Execution worker (Analysis.budget 1 1) (3 * 1)
      (Controller.initial worker (Analysis.budget 1 1)) xs ⟨false, 0, 1⟩ 11 2 := by
    simpa only [Analysis.budget] using execution
  obtain ⟨beforeState, afterState, beforeCost, windowCost, afterCost, beforeSwitches, windowSwitches, afterSwitches,
    _, middle, _, account, _, bound⟩ :=
    Analysis.Results.executed_window (restoreFactor := 3) (well 5) (by decide) valid trace 2 5 (by decide) (by decide)
  refine ⟨beforeState, afterState, windowCost, middle.computed, by omega, ?_⟩
  convert bound using 1; norm_num [Analysis.mass, charges]

-- An empty window preserves a partially spent state and has zero work,
-- even though that state is not the controller's initial state.
example : (0 : ℝ) ≤ 35 := by
  have trace : Controller.Execution worker (Analysis.budget 1 1) (3 * 1)
      ⟨true, 0, 1⟩ (Analysis.segment xs 3 3) ⟨true, 0, 1⟩ 0 0 := by
    simpa only [Analysis.segment, Nat.sub_self, List.take_zero] using
      (Controller.Execution.nil (worker := worker) (budget := Analysis.budget 1 1) (restore := 3 * 1) (s := ⟨true, 0, 1⟩))
  have bound := Analysis.Results.window_minimum (restoreFactor := 3) (well 5) (by decide) valid
    (by decide : 3 ≤ 3) (by decide : 3 ≤ xs.length) trace
  convert bound using 1 <;> norm_num [Analysis.mass]

end RotationBST.Tests.ComboAnalysis
