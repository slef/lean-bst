module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Worker.Replay.Requests.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Worker.Replay.Requests.Results
open HeavyPath.Finger.History

theorem run_append {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool)
    (state : σ) (xs ys : List Nat) :
    run planner side state (xs ++ ys) =
      let first := run planner side state xs
      let last := run planner side first.1 ys
      (last.1, first.2 + last.2) :=
  RotationBST.Combo.Worker.Replay.Requests.run_append planner side state xs ys

theorem program_cost {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool)
    (state : σ) (xs : List Nat) :
    (program planner side state xs).length + 2 * xs.length = (run planner side state xs).2 :=
  RotationBST.Combo.Worker.Replay.Requests.program_cost planner side state xs

theorem source_lift {α : Type} (c : LabelledCursor.Config α) (ops : List Multifinger.Opcode)
    (final : Pointer.Config) (key : Nat)
    (legal : Multifinger.replay ops c.erase = some final) (visit : Visits key ops c.erase) :
    ∃ result : LabelledCursor.Config α,
      Simulation.sourceRun c ops = some result ∧ result.erase = final ∧
        Simulation.Requests.Serves c ops key result :=
  RotationBST.Combo.Worker.Replay.Requests.source_lift c ops final key legal visit

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
          (run planner side (run planner side (planner.initial side) past).1 xs).2 :=
  RotationBST.Combo.Worker.Replay.Requests.planner_source planner side

end RotationBST.Combo.Worker.Replay.Requests.Results

/-- info: abstract audit passed for `RotationBST.Combo.Worker.Replay.Requests.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Worker.Replay.Requests.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
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
  RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Requests.Definitions.Abstract]
