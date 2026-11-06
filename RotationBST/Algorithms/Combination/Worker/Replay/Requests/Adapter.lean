module

public import RotationBST.Algorithms.Combination.Worker.Replay.Requests.Program
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay.Requests
open HeavyPath.Finger.History

/-- Reconstruct the planner's private state from past requests and lift its
exact opcodes to labelled cursors. The fallback supplies total source-interface
correctness on unrelated cursors; executions aligned with the saved tree never
use it. The algorithm is fixed before any future sequence or benchmark. -/
theorem planner_source {α σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) :
    ∃ a : Simulation.Requests.Algorithm α,
      ∀ (past : List Nat) (c : LabelledCursor.Config α) (xs : List Nat),
        (∀ x ∈ past, x < saved.size) →
        c.erase = ⟨planner.tree side (run planner side (planner.initial side) past).1, []⟩ →
        (∀ x ∈ xs, x < saved.size) →
        (a.runFrom past c xs).1 = program planner side (run planner side (planner.initial side) past).1 xs ∧
        (a.runFrom past c xs).2.erase =
          ⟨planner.tree side (run planner side (run planner side (planner.initial side) past).1 xs).1, []⟩ ∧
        (a.runFrom past c xs).1.length + 2 * xs.length =
          (run planner side (run planner side (planner.initial side) past).1 xs).2 := by
  classical
  let history := fun past => (run planner side (planner.initial side) past).1
  have nextHistory : ∀ past x, history (past ++ [x]) = (planner.plan side (history past) x).1 := by
    intro past x
    simp [history, run_append, run]
  have available : ∀ (past : List Nat) (c : LabelledCursor.Config α) (x : Nat),
      (∀ y ∈ past, y < saved.size) → x < saved.size →
      c.erase = ⟨planner.tree side (history past), []⟩ →
      ∃ result : LabelledCursor.Config α,
        Simulation.sourceRun c (planner.plan side (history past) x).2 = some result ∧
        result.erase = ⟨planner.tree side (planner.plan side (history past) x).1, []⟩ ∧
        Simulation.Requests.Serves c (planner.plan side (history past) x).2 x result := by
    intro past c x valid key same
    have size := run_size planner side (planner.initial side) past
      (congrArg Tree.size (planner.initial_tree side)) valid
    apply source_lift c (planner.plan side (history past) x).2 _ x
    · rw [same]
      exact planner.legal side (history past) x size key
    · rw [same]
      exact planner.visits side (history past) x size key
  obtain ⟨fallback⟩ := Simulation.Requests.Results.algorithm_exists α
  let next := fun past (c : LabelledCursor.Config α) x =>
    if good : (∀ y ∈ past, y < saved.size) ∧ x < saved.size ∧
        c.erase = ⟨planner.tree side (history past), []⟩ then
      ((planner.plan side (history past) x).2,
        Classical.choose (available past c x good.1 good.2.1 good.2.2))
    else fallback.step past c x
  let a : Simulation.Requests.Algorithm α := ⟨next, by
    intro past c x live key
    dsimp only [next]
    split_ifs with good
    · exact (Classical.choose_spec (available past c x good.1 good.2.1 good.2.2)).2.2
    · exact fallback.correct past c x live key⟩
  have step : ∀ past c x, (∀ y ∈ past, y < saved.size) → x < saved.size →
      c.erase = ⟨planner.tree side (history past), []⟩ →
      (a.step past c x).1 = (planner.plan side (history past) x).2 ∧
      (a.step past c x).2.erase = ⟨planner.tree side (planner.plan side (history past) x).1, []⟩ := by
    intro past c x valid key same
    change (next past c x).1 = _ ∧ (next past c x).2.erase = _
    dsimp only [next]
    rw [dite_eq_left ⟨valid, key, same⟩]
    exact ⟨rfl, (Classical.choose_spec (available past c x valid key same)).2.1⟩
  have aligned : ∀ (xs past : List Nat) (c : LabelledCursor.Config α),
      (∀ x ∈ past, x < saved.size) → c.erase = ⟨planner.tree side (history past), []⟩ →
      (∀ x ∈ xs, x < saved.size) →
      (a.runFrom past c xs).1 = program planner side (history past) xs ∧
      (a.runFrom past c xs).2.erase = ⟨planner.tree side (run planner side (history past) xs).1, []⟩ := by
    intro xs
    induction xs with
    | nil => intro past c valid same keys; exact ⟨rfl, same⟩
    | cons x xs ih =>
      intro past c valid same keys
      have key := keys x (by simp)
      have first := step past c x valid key same
      have extended : ∀ y ∈ past ++ [x], y < saved.size := by
        intro y member
        rcases List.mem_append.mp member with member | member
        · exact valid y member
        · simpa only [List.mem_singleton.mp member] using key
      have rest := ih (past ++ [x]) (a.step past c x).2 extended
        (by rw [nextHistory]; exact first.2) (fun y member => keys y (by simp [member]))
      constructor
      · simp only [Simulation.Requests.Algorithm.runFrom, program]
        rw [first.1, rest.1, nextHistory]
      · simp only [Simulation.Requests.Algorithm.runFrom, run]
        simpa only [nextHistory] using rest.2
  refine ⟨a, ?_⟩
  intro past c xs valid same keys
  obtain ⟨programEq, finalEq⟩ := aligned xs past c valid same keys
  exact ⟨programEq, finalEq, by rw [programEq]; exact program_cost planner side (history past) xs⟩

end RotationBST.Combo.Worker.Replay.Requests
