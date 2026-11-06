module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Attempts
public import RotationBST.Algorithms.Combination.Refinement.Execution

@[expose] public section
namespace RotationBST.Combo.Refinement.Visits
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads reads_nil reads_append)

/-- A completed controller request preserves the worker's visit even when an
unfinished attempt and snapshot restoration precede its successful retry. -/
theorem service {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (correct : Correct model)
    {budget restore : Nat} {s : Controller.State σ} {x : Nat} {result : Controller.Result σ}
    (run : Controller.Service worker budget restore s x result) (done : result.done = true)
    (boundary : Boundary worker saved.size s.side s.workerState) (valid : x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Requests.Visit actual final x events cost ∧
      Represents model data final result.state.side result.state.workerState ∧
      Boundary worker saved.size result.state.side result.state.workerState ∧
      Reads data events ∧ cost ≤ 15 * result.work ∧ 1 ≤ result.work := by
  cases run with
  | finish first finished =>
    obtain ⟨final, events, cost, visit, finalRep, finalBoundary, reads, bound⟩ :=
      completed model correct first finished boundary valid data actual represented
    exact ⟨final, events, cost, visit, finalRep, finalBoundary, reads, bound, first.positive finished⟩
  | switch first _ second =>
    obtain ⟨interrupted, firstEvents, firstCost, firstTrace, interruptedRep, firstReads, _, firstBound⟩ :=
      Refinement.attempt model first valid data actual represented
    obtain ⟨restored, restoreEvents, restoreCost, restoreTrace, restoredRep, restoreReads, restoreBound⟩ :=
      restart model data stored interrupted s.side _ interruptedRep (!s.side)
    obtain ⟨final, lastEvents, lastCost, visit, finalRep, finalBoundary, lastReads, lastBound⟩ :=
      completed model correct second done (boundary_restart worker saved.size (!s.side)) valid data restored restoredRep
    have positive := second.positive done
    exact ⟨final, firstEvents ++ restoreEvents ++ lastEvents, firstCost + restoreCost + lastCost,
      visit.prepend (firstTrace.append restoreTrace), finalRep, finalBoundary,
      reads_append (reads_append firstReads restoreReads) lastReads, by dsimp only; omega, by dsimp only; omega⟩

/-- Correct worker requests produce a request-serving shared execution. The
factor sixteen includes both the factor-fifteen instruction simulation and
one explicit unit per request; no completion bit is treated as a visit. -/
theorem execution {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (correct : Correct model)
    {budget restore : Nat} {s t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker budget restore s xs t work switches)
    (boundary : Boundary worker saved.size s.side s.workerState) (valid : ∀ x ∈ xs, x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events cost, Shared.Requests.Execution actual xs final events cost ∧
      Represents model data final t.side t.workerState ∧ Boundary worker saved.size t.side t.workerState ∧
      Reads data events ∧ cost ≤ 16 * work := by
  induction run generalizing actual with
  | nil => exact ⟨actual, [], 0, .nil, represented, boundary, reads_nil data, Nat.le_refl _⟩
  | @cons s t x xs work switches done tail ih =>
    obtain ⟨middle, firstEvents, firstCost, visit, middleRep, middleBoundary, firstReads, firstBound, positive⟩ :=
      service model correct (Controller.serve_service worker budget restore s x) done boundary (valid x (by simp))
        paid data stored actual represented
    obtain ⟨final, lastEvents, lastCost, last, finalRep, finalBoundary, lastReads, lastBound⟩ :=
      ih middleBoundary (fun y member => valid y (List.mem_cons_of_mem x member)) middle middleRep
    exact ⟨final, firstEvents ++ lastEvents, 1 + firstCost + lastCost, .cons visit last, finalRep, finalBoundary,
      reads_append firstReads lastReads, by omega⟩

end RotationBST.Combo.Refinement.Visits
