module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Combination.AbstractBridge

@[expose] public section
/-! Tango's interruptible combination input. The initialization allowance is
`chargeFactor reference * n`, growing as n log log n for balanced references.
It remains to remove that factor from startup for GreedyASS Theorem 4.3. -/
namespace RotationBST.Tango.Combination.Results
open Combo

theorem factor_lower (reference : Tree) :
    64 * (14 * Real.logb 2 (height reference) + 6) ≤ (chargeFactor reference : ℝ) :=
  RotationBST.Tango.Combination.factor_lower reference

theorem factor_pos (reference : Tree) : 0 < chargeFactor reference :=
  RotationBST.Tango.Combination.factor_pos reference

theorem balanced_factor (n : Nat) : chargeFactor (balanced n) ≤
    ⌈64 * (14 * Real.logb 2 (Nat.log2 n + 1) + 6)⌉₊ :=
  RotationBST.Tango.Combination.balanced_factor n

theorem worker {reference : Tree} (p : Policy reference) (saved : Tree) (same : saved.size = reference.size) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor reference * saved.size) 1 20 (fun _ => Charges.interleave (chargeFactor reference) reference) :=
  RotationBST.Tango.Combination.worker p saved same

theorem competitive_worker {reference : Tree} (p : Policy reference) (saved : Tree) (same : saved.size = reference.size) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor reference * saved.size) 1 20 (fun _ => Charges.interleave (chargeFactor reference) reference) ∧
      ∀ (s t : Tree) (xs : List Nat) (k : Nat), s.size = reference.size →
        RotationBST.Execution s xs t k → ∀ side,
          ∃ final cost, Worker.Requests (Worker.Replay.worker planner) side
            ((Worker.Replay.worker planner).restart side) xs final cost ∧
            (cost : ℝ) ≤ (4 * chargeFactor reference : Nat) * (xs.length + k : Nat) +
              (chargeFactor reference * saved.size : Nat) :=
  RotationBST.Tango.Combination.competitive_worker p saved same

theorem balanced_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (chargeFactor (balanced saved.size) * saved.size) 1 20
        (fun _ => Charges.interleave (chargeFactor (balanced saved.size)) (balanced saved.size)) :=
  RotationBST.Tango.Combination.balanced_worker saved

theorem linear_factor_lower (reference : Tree) :
    64 * (17 * Real.logb 2 (height reference) + 6) ≤ (linearChargeFactor reference : ℝ) :=
  RotationBST.Tango.Combination.linear_factor_lower reference

theorem balanced_linear_factor (n : Nat) : linearChargeFactor (balanced n) ≤
    2 * ⌈64 * (14 * Real.logb 2 (Nat.log2 n + 1) + 6)⌉₊ :=
  RotationBST.Tango.Combination.balanced_linear_factor n

theorem linear_balanced_worker (saved : Tree) :
    ∃ planner : Worker.Replay.Planner (List Nat × Pointer.Lazy.Online.State) saved,
      Analysis.WellBehaved (Worker.Replay.worker planner) saved.size
        (2816 * saved.size) 1 20
        (fun _ => Charges.interleave (linearChargeFactor (balanced saved.size)) (balanced saved.size)) :=
  RotationBST.Tango.Combination.linear_balanced_worker saved

end RotationBST.Tango.Combination.Results

/-- info: abstract audit passed for `RotationBST.Tango.Combination.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Combination.Results allowing [
  RotationBST.Models.Rotation.Abstract,
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
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
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
  RotationBST.Algorithms.Tango.Combination.Definitions.Abstract]
