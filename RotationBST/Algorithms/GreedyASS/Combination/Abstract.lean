module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Combination.AbstractBridge

@[expose] public section
/-! One prepared GreedyASS–Tango policy satisfies all fixed-tree, weighted,
and offline-comparison bounds with a linear startup allowance. The
logarithmic worst-case transformation and the abstract BST-operation
counterpart of Theorem 4.3 are in `Combination/Deamortized`. -/
namespace RotationBST.Geometric.GreedyASS.Combination.Results
open Combo

/-- One fixed GreedyASS replay worker has the full combination contract for
every same-size lazy-finger reference tree. This is the GreedyASS input to
Theorem 4.3; the Tango input and final deamortized combination are separate.
Planning and instruction-log storage are abstract BST resources. -/
theorem greedy_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      ∀ t : Tree, t.size = saved.size →
        Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
          (46225920 * saved.size) 1 20 (fun _ => Charges.lazyFinger 46225920 t) :=
  RotationBST.Geometric.GreedyASS.Combination.greedy_worker saved

theorem policy_exists (saved : Tree) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    Nonempty (Policy saved fields oldData) :=
  RotationBST.Geometric.GreedyASS.Combination.policy_exists saved nonempty fields oldData

theorem tree_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (reference : Tree) (same : reference.size = saved.size)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.finalTree xs) (p.cost xs) ∧
      (p.cost xs : ℝ) ≤ 1307904 * min (46225920 * (LazyFinger.cost reference xs : ℝ))
        (Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
          (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat)) +
        2531968 * overhead saved :=
  RotationBST.Geometric.GreedyASS.Combination.Policy.tree_bound p reference same xs valid

theorem optimal_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.finalTree xs) (p.cost xs) ∧
      (p.cost xs : ℝ) ≤ 1307904 * min (46225920 * (LazyFinger.optimalCost saved.size xs : ℝ))
        (Tango.Combination.linearChargeFactor (Tango.balanced saved.size) *
          (xs.length + Wilber.interleave (Tango.balanced saved.size) xs : Nat)) +
        2531968 * overhead saved :=
  RotationBST.Geometric.GreedyASS.Combination.Policy.optimal_bound p xs valid

theorem worker_bound {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (reference : Tree) (same : reference.size = saved.size)
    (select : Bool → Bool) :
    Analysis.WellBehaved (Worker.Replay.worker p.implementation.planner) saved.size
      (Online.Replay.overheadFactor 1 20 57 * overhead saved) 1 21
      (Online.Replay.scaledCharges (Online.Replay.chargeFactor 1 20 57)
        (fun side => charges saved reference (select side))) :=
  RotationBST.Geometric.GreedyASS.Combination.Policy.worker_bound p reference same select

theorem weighted_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (start : Nat) (key : start < saved.size)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) :
    (p.cost xs : ℝ) ≤ 1307904 * min
        (184903680 * WeightedFinger.optimalCostFrom saved.size start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
      3839872 * overhead saved :=
  RotationBST.Geometric.GreedyASS.Combination.Policy.weighted_competitive p start key size execution

theorem weights_competitive {saved : Tree} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Policy saved fields oldData) (start : Nat) (key : start < saved.size)
    (w : Nat → ℝ) (positive : ∀ x < saved.size, 0 < w x)
    {s t : Tree} {xs : List Nat} {k : Nat} (size : s.size = saved.size)
    (execution : RotationBST.Execution s xs t k) :
    (p.cost xs : ℝ) ≤ 1307904 * min
        (184903680 * WeightedFinger.costFrom w start xs)
        ((4 * Tango.Combination.linearChargeFactor (Tango.balanced saved.size) : Nat) * (xs.length + k : Nat)) +
      3839872 * overhead saved :=
  RotationBST.Geometric.GreedyASS.Combination.Policy.weights_competitive p start key w positive size execution

end RotationBST.Geometric.GreedyASS.Combination.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Combination.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Combination.Results allowing [
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
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract]
