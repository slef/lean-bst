module

public import RotationBST.Algorithms.Deamortization.Finger.Online
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

/-- The persistent scheduler serves every source request with a logarithmic
window budget. Unexecuted physical work and the source simulation's potential
remain in the total accounting, so no future work pays for an earlier request. -/
theorem transform_spec {α : Type} {sourcePolicy : Simulation.Policy α} {scheduler : Scheduler.Policy}
    (bounded : Simulation.PolicyBounded (fun _ => 1) sourcePolicy) {budget : Nat}
    (schedulerValid : Scheduler.PolicyValid budget scheduler) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ (out : Scheduler.Output) (planned : PreparedOutput α),
      prepare sourcePolicy a past c s keys = some planned ∧
      transform sourcePolicy scheduler a past c s keys = some out ∧
      out.state.planned = ⟨planned.history.pair.tree, []⟩ ∧ Scheduler.Valid budget out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
      Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
        (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.instructions.length + 5 * out.state.pending.length + 5 * planned.history.potential ≤
        310 * (a.runFrom past c keys).1.length + 5 * s.potential ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      ∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget := by
  obtain ⟨planned, prepared, _, _, keysEq, ready, plannedWork⟩ :=
    prepare_spec bounded a past valid budgetBound keys validKeys
  obtain ⟨out, completed, final, nextValid, replay, execution, account, work, count, total, costs, _⟩ :=
    Scheduler.run_spec schedulerValid (initial_valid bounded valid budgetBound) ready
  have length : planned.requests.length = keys.length := by
    simpa only [List.length_map] using congrArg List.length keysEq
  refine ⟨out, planned, prepared, ?_, final, nextValid, replay, ?_, ?_, ?_, ?_, costs⟩
  · simpa only [transform, prepared, Option.bind_some] using completed
  · simpa only [keysEq, length, Scheduler.initial] using execution
  · change out.state.pending.length + out.consumed =
      0 + (planned.requests.map (fun request => request.instructions.length)).sum at account
    omega
  · exact count.trans length
  · simpa only [length] using total

/-- Minimum-relative credit retains the pending-work charge for the same online scheduler. -/
theorem transform_excess {α : Type} {sourcePolicy : Simulation.Policy α} {scheduler : Scheduler.Policy}
    (bounded : Simulation.PolicyBounded (fun _ => 1) sourcePolicy) {budget : Nat}
    (schedulerValid : Scheduler.PolicyValid budget scheduler) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) {c : LabelledCursor.Config α} {s : State α}
    (valid : Simulation.ConfigValid (fun _ => 1) c s)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ (out : Scheduler.Output) (planned : PreparedOutput α),
      prepare sourcePolicy a past c s keys = some planned ∧
      transform sourcePolicy scheduler a past c s keys = some out ∧
      out.state.planned = ⟨planned.history.pair.tree, []⟩ ∧ Scheduler.Valid budget out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
      Scheduler.ServedStream ⟨s.pair.tree, []⟩ keys out.state.cursor out.instructions out.costs ∧
      Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
        (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.instructions.length + 5 * out.state.pending.length + 5 * Simulation.Minimum.excess (fun _ => 1) planned.source planned.history ≤
        1240 * (a.runFrom past c keys).1.length + 5 * Simulation.Minimum.excess (fun _ => 1) c s ∧
      out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
      ∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget := by
  obtain ⟨planned, prepared, _, _, keysEq, ready, plannedWork⟩ :=
    prepare_excess bounded a past valid budgetBound keys validKeys
  obtain ⟨out, completed, final, nextValid, replay, execution, account, work, count, total, costs, _⟩ :=
    Scheduler.run_spec schedulerValid (initial_valid bounded valid budgetBound) ready
  have length : planned.requests.length = keys.length := by
    simpa only [List.length_map] using congrArg List.length keysEq
  refine ⟨out, planned, prepared, ?_, final, nextValid, replay, ?_, ?_, ?_, ?_, ?_, costs⟩
  · simpa only [transform, prepared, Option.bind_some] using completed
  · have served := Scheduler.run_served schedulerValid (initial_valid bounded valid budgetBound) ready completed
    simpa only [keysEq, Scheduler.initial] using served
  · simpa only [keysEq, length, Scheduler.initial] using execution
  · change out.state.pending.length + out.consumed =
      0 + (planned.requests.map (fun request => request.instructions.length)).sum at account
    omega
  · exact count.trans length
  · simpa only [length] using total

end RotationBST.Deamortization.Finger
