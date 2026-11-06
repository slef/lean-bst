module

public import RotationBST.Algorithms.Combination.Worker.Replay.Execution

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

variable {σ : Type} {saved : Tree} (planner : Planner σ saved)

theorem ready_size (side : Bool) (state : State σ) (ready : Ready planner side state) :
    (cursor planner side state).tree.size = saved.size := by
  cases state with
  | boundary state => exact ready
  | running next current ops =>
    obtain ⟨_, _, shapes⟩ := (Multifinger.Replay.Results.physical ready.2).rotations
    exact shapes.size_eq.trans ready.1

theorem step_ready (side : Bool) (state : State σ) (x : Nat)
    (ready : Ready planner side state) (valid : x < saved.size) :
    Ready planner side ((worker planner).step side state x).1 := by
  cases state with
  | boundary state => exact ⟨plan_size planner side state x ready valid, planner.legal side state x ready valid⟩
  | running next current ops =>
    cases ops with
    | nil => exact ready.1
    | cons op ops =>
      obtain ⟨moved, first, rest⟩ := Option.bind_eq_some_iff.mp ready.2
      simpa only [worker, step, first, Ready] using And.intro ready.1 rest

theorem step_cursor (side : Bool) (state : State σ) (x : Nat)
    (ready : Ready planner side state) :
    match instruction state with
    | none => cursor planner side ((worker planner).step side state x).1 = cursor planner side state
    | some op => perform op (cursor planner side state) = some (cursor planner side ((worker planner).step side state x).1) := by
  cases state with
  | boundary state => rfl
  | running next current ops =>
    cases ops with
    | nil => exact (Option.some.inj ready.2).symm
    | cons op ops =>
      obtain ⟨moved, first, _⟩ := Option.bind_eq_some_iff.mp ready.2
      simp only [instruction, cursor, worker, step, first]

end RotationBST.Combo.Worker.Replay
