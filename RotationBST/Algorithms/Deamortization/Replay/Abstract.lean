module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Replay.AbstractBridge

@[expose] public section
namespace RotationBST.Deamortization.Replay.Results

theorem deamortize {σ : Type} {saved : Tree} (planner : Combo.Worker.Replay.Planner σ saved)
    (side : Bool) (nonempty : saved ≠ .nil) :
    ∃ (initial : Tree) (startup : Nat) (program : List Nat → Option Scheduler.Output),
      Pointer.Trace ⟨saved, []⟩ ⟨initial, []⟩ startup ∧ startup ≤ 16 * saved.size ∧
      (∀ keys, (∀ x ∈ keys, x < saved.size) →
        ∃ out, program keys = some out ∧
          Multifinger.replay out.instructions ⟨initial, []⟩ = some out.state.cursor ∧
          Scheduler.ServedStream ⟨initial, []⟩ keys out.state.cursor out.instructions out.costs ∧
          Multifinger.Execution (Scheduler.cursorState ⟨initial, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          out.costs.sum ≤ 1240 * (Combo.Worker.Replay.run planner side (planner.initial side) keys).2 ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size) ∧
      (∀ xs ys out, program (xs ++ ys) = some out →
        ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
          first.costs <+: out.costs) :=
  RotationBST.Deamortization.Replay.deamortize planner side nonempty

end RotationBST.Deamortization.Replay.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Replay.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Replay.Results allowing [
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
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Definitions.Abstract]
