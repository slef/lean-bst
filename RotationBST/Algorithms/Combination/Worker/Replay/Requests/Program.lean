module

public import RotationBST.Algorithms.Combination.Worker.Replay.Requests.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Replay.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay.Requests
open HeavyPath.Finger.History

/-- Pure planner execution composes through its actual private successor state. -/
theorem run_append {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool)
    (state : σ) (xs ys : List Nat) :
    run planner side state (xs ++ ys) =
      let first := run planner side state xs
      let last := run planner side first.1 ys
      (last.1, first.2 + last.2) := by
  induction xs generalizing state with
  | nil => simp [run]
  | cons x xs ih => simp [run, ih, Nat.add_assoc]

/-- The only difference between recorded instruction cost and worker cost is
exactly two bookkeeping steps per completed request. -/
theorem program_cost {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool)
    (state : σ) (xs : List Nat) :
    (program planner side state xs).length + 2 * xs.length = (run planner side state xs).2 := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    have rest := ih (planner.plan side state x).1
    simp only [program, run, List.length_append, List.length_cons]
    omega

/-- Lift a recorded visit without changing any instruction or node label. -/
theorem source_lift {α : Type} (c : LabelledCursor.Config α) (ops : List Multifinger.Opcode)
    (final : Pointer.Config) (key : Nat)
    (legal : Multifinger.replay ops c.erase = some final) (visit : Visits key ops c.erase) :
    ∃ result : LabelledCursor.Config α,
      Simulation.sourceRun c ops = some result ∧ result.erase = final ∧
        Simulation.Requests.Serves c ops key result := by
  have mapped := (Simulation.Requests.Results.source_erase c ops).trans legal
  obtain ⟨result, completed, erased⟩ := Option.map_eq_some_iff.mp mapped
  obtain ⟨before, after, visited, split, reached, target⟩ := visit
  have mappedPrefix := (Simulation.Requests.Results.source_erase c before).trans reached
  obtain ⟨middle, first, same⟩ := Option.map_eq_some_iff.mp mappedPrefix
  have last : Simulation.sourceRun middle after = some result := by
    rw [split, Simulation.Requests.source_append, first, Option.bind_some] at completed
    exact completed
  exact ⟨result, completed, erased, before, after, middle, split, first, by rw [same]; exact target, last⟩

end RotationBST.Combo.Worker.Replay.Requests
