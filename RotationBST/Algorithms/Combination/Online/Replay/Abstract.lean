module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Online.Replay.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Online.Replay.Results

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}

theorem implementation_exists (p : Prepared model budget restore fields oldData) : Nonempty (Implementation p) :=
  RotationBST.Combo.Online.Replay.implementation_exists p

theorem run_bound (p : Prepared model budget restore fields oldData) (implementation : Implementation p) (side : Bool)
    (s : Option (Online.State model p.data budget)) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    (Worker.Replay.run implementation.planner side s xs).1 = (execute p s xs).1 ∧
      (Worker.Replay.run implementation.planner side s xs).2 ≤ 2 * (execute p s xs).2 :=
  RotationBST.Combo.Online.Replay.run_bound p implementation side s xs valid

theorem requests (p : Prepared model budget restore fields oldData) (implementation : Implementation p) (side : Bool) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ cost, Worker.Requests (Worker.Replay.worker implementation.planner) side
      ((Worker.Replay.worker implementation.planner).restart side) xs
      (.boundary (execute p none xs).1) cost ∧ cost ≤ 2 * (execute p none xs).2 :=
  RotationBST.Combo.Online.Replay.requests p implementation side xs valid

theorem single (p : Prepared model budget restore fields oldData) (implementation : Implementation p)
    (side : Bool) (state : Worker.Replay.State (Option (Online.State model p.data budget))) (x : Nat)
    (boundary : Refinement.Visits.Boundary (Worker.Replay.worker implementation.planner) saved.size side state)
    (valid : x < saved.size) :
    ∃ final cost, Worker.Access (Worker.Replay.worker implementation.planner) side state x final cost ∧
      cost ≤ 1140224 * saved.size + 16768 * (2 * budget + restore) :=
  RotationBST.Combo.Online.Replay.single p implementation side state x boundary valid

theorem minimum_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ cost, Worker.Requests (Worker.Replay.worker implementation.planner) side
      ((Worker.Replay.worker implementation.planner).restart side) xs
      (.boundary (execute p none xs).1) cost ∧
      (cost : ℝ) ≤ 1140224 * (saved.size : ℝ) +
        16768 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Online.Replay.minimum_bound well p implementation side xs valid

theorem well_behaved_selection {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (size : saved.size ≤ overhead) (select : Bool → Bool) :
    Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
      (overheadFactor C₀ C₁ restoreFactor * overhead) C₀ (C₁ + 1)
      (scaledCharges (chargeFactor C₀ C₁ restoreFactor) (fun side => charges (select side))) :=
  RotationBST.Combo.Online.Replay.well_behaved_selection well p implementation size select

theorem well_behaved {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (size : saved.size ≤ overhead) :
    Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
      (overheadFactor C₀ C₁ restoreFactor * overhead) C₀ (C₁ + 1)
      (scaledCharges (chargeFactor C₀ C₁ restoreFactor) charges) :=
  RotationBST.Combo.Online.Replay.well_behaved well p implementation size

theorem combine {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∃ implementation : Implementation p,
        Refinement.Visits.Correct (Worker.Replay.model implementation.planner) ∧
        Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
          (overheadFactor C₀ C₁ 57 * overhead) C₀ (C₁ + 1)
          (scaledCharges (chargeFactor C₀ C₁ 57) charges) :=
  RotationBST.Combo.Online.Replay.combine model correct well nonempty size fields oldData

end RotationBST.Combo.Online.Replay.Results

/-- info: abstract audit passed for `RotationBST.Combo.Online.Replay.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Online.Replay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Initialization.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
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
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Requests.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Erasure.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.BSTDeque.Definitions.Abstract,
  RotationBST.Structures.BSTDeque.Boundary.Definitions.Abstract,
  RotationBST.Structures.Tendon.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Definitions.Abstract,
  RotationBST.Structures.FingerHand.Packed.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Startup.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Online.Algorithm.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Replay.Model.Abstract,
  RotationBST.Algorithms.Combination.Online.Replay.Definitions.Abstract]
