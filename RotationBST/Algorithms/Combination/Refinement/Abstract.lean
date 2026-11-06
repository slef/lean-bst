module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Refinement.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Refinement.Results
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads)

theorem worker_step {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (data : Nat → Nat) (actual : Shared.State Nat 2)
    (side : Bool) (state : σ) (represented : Represents model data actual side state)
    (x : Nat) (valid : x < saved.size) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final side (worker.step side state x).1 ∧ Reads data events ∧
      final.position 1 = actual.position 1 ∧ cost ≤ 15 :=
  RotationBST.Combo.Refinement.worker_step model data actual side state represented x valid

theorem attempt {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {side : Bool} {x fuel work : Nat} {state : σ} {result : Controller.Attempt σ}
    (run : Controller.AttemptRun worker side x fuel state result work) (valid : x < saved.size)
    (data : Nat → Nat) (actual : Shared.State Nat 2) (represented : Represents model data actual side state) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents model data final side result.state ∧
      Reads data events ∧ final.position 1 = actual.position 1 ∧ cost ≤ 15 * work :=
  RotationBST.Combo.Refinement.attempt model run valid data actual represented

theorem restart {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (side : Bool) (state : σ) (represented : Represents model data actual side state)
    (nextSide : Bool) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final nextSide (worker.restart nextSide) ∧ Reads data events ∧ cost ≤ 841 * saved.size :=
  RotationBST.Combo.Refinement.restart model data stored actual side state represented nextSide

theorem service {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {budget restore : Nat} {s : Controller.State σ} {x : Nat} {result : Controller.Result σ}
    (run : Controller.Service worker budget restore s x result) (valid : x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final result.state.side result.state.workerState ∧ Reads data events ∧ cost ≤ 15 * result.work :=
  RotationBST.Combo.Refinement.service model run valid paid data stored actual represented

theorem execution {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {budget restore : Nat} {s t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker budget restore s xs t work switches) (valid : ∀ x ∈ xs, x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final t.side t.workerState ∧ Reads data events ∧ cost ≤ 15 * work :=
  RotationBST.Combo.Refinement.execution model run valid paid data stored actual represented

theorem execution_bound {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    {t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker (Analysis.budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (Analysis.budget overhead C₁)) xs t work switches)
    (valid : ∀ x ∈ xs, x < saved.size) (paid : 841 * saved.size ≤ 15 * (restoreFactor * overhead))
    (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual false (worker.restart false)) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents model data final t.side t.workerState ∧
      Reads data events ∧ (cost : ℝ) ≤ 15 * (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Refinement.execution_bound model well run valid paid data stored actual represented

theorem startup {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (data : Nat → Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ ready snapshotData saveEvents saveCost final events cost endState work switches,
      Snapshot.Startup.Execution saved saved.size fields data ready saveEvents saveCost ∧
      Snapshot.CellIO.Stored saved snapshotData ∧
      Controller.run worker (Analysis.budget overhead C₁) (57 * overhead)
        (Controller.initial worker (Analysis.budget overhead C₁)) xs = some (endState, work) ∧
      Controller.Execution worker (Analysis.budget overhead C₁) (57 * overhead)
        (Controller.initial worker (Analysis.budget overhead C₁)) xs endState work switches ∧
      Shared.Trace ready final events cost ∧ Represents model snapshotData final endState.side endState.workerState ∧
      Reads snapshotData events ∧ (saveCost + cost : Nat) ≤ (1088 * saved.size : ℝ) + 15 * (C₁ + 1 + 57 : Nat) *
        (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Refinement.startup model well nonempty size fields data xs valid

end RotationBST.Combo.Refinement.Results

/-- info: abstract audit passed for `RotationBST.Combo.Refinement.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Refinement.Results allowing [
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
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract]
