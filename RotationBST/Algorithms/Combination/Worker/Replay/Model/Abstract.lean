module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Worker.Replay.ModelFacts

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

variable {σ : Type} {saved : Tree} (planner : Planner σ saved)

theorem model_ready_size (side : Bool) (state : State σ) (ready : Ready planner side state) :
    (cursor planner side state).tree.size = saved.size :=
  ready_size planner side state ready

theorem model_step_ready (side : Bool) (state : State σ) (x : Nat)
    (ready : Ready planner side state) (valid : x < saved.size) :
    Ready planner side ((worker planner).step side state x).1 :=
  step_ready planner side state x ready valid

theorem model_step_cursor (side : Bool) (state : State σ) (x : Nat)
    (ready : Ready planner side state) :
    match instruction state with
    | none => cursor planner side ((worker planner).step side state x).1 = cursor planner side state
    | some op => perform op (cursor planner side state) = some (cursor planner side ((worker planner).step side state x).1) :=
  step_cursor planner side state x ready

/-- A causal single-opcode interpretation of the interruptible trace worker.
The pending log is abstract state; no real-world space bound is asserted. -/
def model : Refinement.WorkerModel (worker planner) saved where
  cursor := cursor planner
  Ready := Ready planner
  instruction := fun _ state _ => instruction state
  restart_ready := fun side => congrArg Tree.size (planner.initial_tree side)
  restart_cursor := fun side => congrArg (fun t => Pointer.Config.mk t []) (planner.initial_tree side)
  size := model_ready_size planner
  step_ready := model_step_ready planner
  step_cursor := fun side state x ready _ => model_step_cursor planner side state x ready

end RotationBST.Combo.Worker.Replay

/-- info: abstract audit passed for `RotationBST.Combo.Worker.Replay`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Worker.Replay allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract]
