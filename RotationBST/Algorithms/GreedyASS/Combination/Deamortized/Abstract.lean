module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Combination.Deamortized.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Combination.Deamortized.Results

theorem policy_exists {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (nonempty : saved ≠ .nil) : Nonempty (Deamortized p) :=
  RotationBST.Geometric.GreedyASS.Combination.deamortized_exists p nonempty

theorem total_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) {keys : List Nat}
    (valid : ∀ x ∈ keys, x < saved.size) {out : Deamortization.Scheduler.Output}
    (completed : d.program keys = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 2480 * p.cost keys :=
  RotationBST.Geometric.GreedyASS.Combination.Deamortized.total_bound d valid completed

theorem weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
        3839872 * overhead saved) :=
  RotationBST.Geometric.GreedyASS.Combination.Deamortized.weighted_competitive d start key size execution completed

theorem weights_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {p : Policy saved fields oldData} (d : Deamortized p) (start : Nat) (key : start < saved.size)
    (w : Nat → ℝ) (positive : ∀ x < saved.size, 0 < w x)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.costFrom w start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
        3839872 * overhead saved) :=
  RotationBST.Geometric.GreedyASS.Combination.Deamortized.weights_competitive d start key w positive size execution completed

theorem linear_weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds}
    {oldData : Nat → Nat} {p : Policy saved fields oldData} (d : Deamortized p)
    (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) {out : Deamortization.Scheduler.Output}
    (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
      (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((8 * ⌈64 * (14 * Real.logb 2 (Nat.log2 saved.size + 1) + 6)⌉₊ : Nat) * (xs.length + k : Nat)) +
        3839872 * (46225920 * saved.size : Nat)) :=
  RotationBST.Geometric.GreedyASS.Combination.Deamortized.linear_weighted_competitive d start key size execution completed

theorem combined (saved : Tree) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Policy saved fields oldData, ∃ d : Deamortized p,
      ∀ xs : List Nat, (∀ x ∈ xs, x < saved.size) →
        ∃ out, d.program xs = some out ∧
          Deamortization.Scheduler.ServedStream ⟨d.initial, []⟩ xs out.state.cursor out.instructions out.costs ∧
          out.costs.length = xs.length ∧ out.costs.sum = xs.length + out.instructions.length ∧
          (∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size) ∧
          ∀ (start : Nat), start < saved.size → ∀ (s t : Tree) (k : Nat), s.size = saved.size →
            RotationBST.Execution s xs t k →
              (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 2480 *
                (1307904 * min (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
                  ((8 * ⌈64 * (14 * Real.logb 2 (Nat.log2 saved.size + 1) + 6)⌉₊ : Nat) * (xs.length + k : Nat)) +
                  3839872 * (46225920 * saved.size : Nat)) :=
  RotationBST.Geometric.GreedyASS.Combination.combined saved nonempty fields oldData

end RotationBST.Geometric.GreedyASS.Combination.Deamortized.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Combination.Deamortized.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Combination.Deamortized.Results allowing [
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
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
  RotationBST.Algorithms.Combination.Charges.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Startup.Definitions.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Pointer.Routing.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Access.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Maintenance.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Requests.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Erasure.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.BSTDeque.Definitions.Abstract,
  RotationBST.Structures.BSTDeque.Boundary.Definitions.Abstract,
  RotationBST.Structures.Tendon.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Packed.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Startup.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Algorithm.Abstract,
  RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Abstract,
  RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Bounds.Interleave.Transition.Defs,
  RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Traces,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Algorithms.Tango.Combination.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Combination.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract,
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
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
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Combination.Deamortized.Definitions.Abstract]
