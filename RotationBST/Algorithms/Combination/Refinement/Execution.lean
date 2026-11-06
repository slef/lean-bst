module

public import RotationBST.Algorithms.Combination.Refinement.Attempts
public import RotationBST.Algorithms.Combination.Controller.Progress
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Interrupted

@[expose] public section
namespace RotationBST.Combo.Refinement
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads reads_append)

/-- A restart is a real snapshot load on the current shared tree, including
navigation from an interrupted worker position. No finger is teleported. -/
theorem restart {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (side : Bool) (state : σ) (represented : Represents model data actual side state)
    (nextSide : Bool) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final nextSide (worker.restart nextSide) ∧ Reads data events ∧ cost ≤ 841 * saved.size := by
  have same : actual.tree.erase.size = saved.size := by
    rw [represented.2.2.1]
    exact model.size side state represented.1
  obtain ⟨final, events, cost, trace, finalValid, shape, atRoot, reads, bound⟩ :=
    Snapshot.Streaming.Refinement.load_interrupted saved data stored actual represented.2.1 same
  exact ⟨final, events, cost, trace, ⟨model.restart_ready nextSide, finalValid,
    by simpa only [model.restart_cursor, Pointer.Config.tree, Pointer.plug] using shape,
    by simpa only [model.restart_cursor] using atRoot⟩, reads, bound⟩

/-- Refine both branches of one controller service. An actual snapshot load
separates a failed attempt from the other worker's retry. The restore charge
must cover its cost under the same factor-fifteen simulation bound. -/
theorem service {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {budget restore : Nat} {s : Controller.State σ} {x : Nat} {result : Controller.Result σ}
    (run : Controller.Service worker budget restore s x result) (valid : x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final result.state.side result.state.workerState ∧ Reads data events ∧ cost ≤ 15 * result.work := by
  cases run with
  | finish first _ =>
    obtain ⟨final, events, cost, trace, finalRep, reads, _, bound⟩ := attempt model first valid data actual represented
    exact ⟨final, events, cost, trace, finalRep, reads, bound⟩
  | switch first _ second =>
    obtain ⟨interrupted, firstEvents, firstCost, firstTrace, interruptedRep, firstReads, _, firstBound⟩ :=
      attempt model first valid data actual represented
    obtain ⟨restored, restoreEvents, restoreCost, restoreTrace, restoredRep, restoreReads, restoreBound⟩ :=
      restart model data stored interrupted s.side _ interruptedRep (!s.side)
    obtain ⟨final, lastEvents, lastCost, lastTrace, finalRep, lastReads, _, lastBound⟩ :=
      attempt model second valid data restored restoredRep
    exact ⟨final, firstEvents ++ restoreEvents ++ lastEvents, firstCost + restoreCost + lastCost,
      (firstTrace.append restoreTrace).append lastTrace, finalRep,
      reads_append (reads_append firstReads restoreReads) lastReads, by dsimp only; omega⟩

/-- The entire abstract controller execution has a shared-node trace. Every
worker opcode, snapshot read, root move, and metadata update is charged; saved
cells remain unchanged through all switches. This theorem concerns physical
instruction refinement; a request-visit contract is a separate obligation. -/
theorem execution {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {budget restore : Nat} {s t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker budget restore s xs t work switches) (valid : ∀ x ∈ xs, x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final t.side t.workerState ∧ Reads data events ∧ cost ≤ 15 * work := by
  induction run generalizing actual with
  | nil => exact ⟨actual, [], 0, .refl, represented, Snapshot.Streaming.Refinement.reads_nil data, Nat.le_refl _⟩
  | @cons s t x xs work switches done tail ih =>
    obtain ⟨middle, firstEvents, firstCost, firstTrace, middleRep, firstReads, firstBound⟩ :=
      service model (Controller.serve_service worker budget restore s x) (valid x (by simp)) paid data stored actual represented
    obtain ⟨final, lastEvents, lastCost, lastTrace, finalRep, lastReads, lastBound⟩ :=
      ih (fun y member => valid y (List.mem_cons_of_mem x member)) middle middleRep
    exact ⟨final, firstEvents ++ lastEvents, firstCost + lastCost, firstTrace.append lastTrace,
      finalRep, reads_append firstReads lastReads, by omega⟩

end RotationBST.Combo.Refinement
