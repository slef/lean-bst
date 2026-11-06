module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Refinement.Attempts
public import RotationBST.Algorithms.Combination.Worker.Rounds
public import RotationBST.Structures.TreeBuffer.Shared.Requests.Visits

@[expose] public section
namespace RotationBST.Combo.Refinement.Visits
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads reads_nil reads_append)

theorem boundary_restart {σ : Type} (worker : Controller.Worker σ) (n : Nat) (side : Bool) :
    Boundary worker n side (worker.restart side) := ⟨[], 0, .nil, by simp⟩

theorem Boundary.next {σ : Type} {worker : Controller.Worker σ} {n : Nat} {side : Bool} {state final : σ} {x work : Nat}
    (boundary : Boundary worker n side state) (valid : x < n) (run : Worker.Access worker side state x final work) :
    Boundary worker n side final := by
  obtain ⟨earlier, spent, previous, validEarlier⟩ := boundary
  refine ⟨earlier ++ [x], spent + work, ?_, ?_⟩
  · simpa only [Nat.add_zero] using previous.append (Worker.Requests.cons run .nil)
  · intro y member
    rcases List.mem_append.mp member with member | member
    · exact validEarlier y member
    · simpa only [List.mem_singleton.mp member] using valid

/-- A final cursor visit is also a visit along the exact consumed attempt,
including the zero-step case. No completion-at-the-key convention is assumed. -/
theorem seen_final {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {side : Bool} {x fuel work : Nat}
    {state : σ} {result : Controller.Attempt σ}
    (run : Controller.AttemptRun worker side x fuel state result work)
    (key : (model.cursor side result.state).key? = some x) : Seen model side x work state := by
  induction run with
  | exhausted => exact key
  | done operation =>
      apply Or.inr
      simpa only [Seen, operation] using key
  | more operation _ ih =>
      simp only [Nat.add_comm 1, Seen]
      exact Or.inr (by simpa only [operation] using ih key)

private theorem represented_key {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : WorkerModel worker saved} {data : Nat → Nat} {actual : Shared.State Nat 2} {side : Bool} {state : σ} {x : Nat}
    (represented : Represents model data actual side state) (seen : (model.cursor side state).key? = some x) :
    actual.position 0 = x := Option.some.inj (represented.2.2.2.symm.trans seen)

/-- The same step-by-step lifting preserves any visit in the attempted worker
path, with the entire before/after trace and its exact physical cost. -/
theorem attempt {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {side : Bool} {x fuel work : Nat} {state : σ} {result : Controller.Attempt σ}
    (run : Controller.AttemptRun worker side x fuel state result work) (valid : x < saved.size)
    (data : Nat → Nat) (actual : Shared.State Nat 2) (represented : Represents model data actual side state) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents model data final side result.state ∧
      Reads data events ∧ cost ≤ 15 * work ∧
      (Seen model side x work state → Shared.Requests.Visit actual final x events cost) := by
  induction run generalizing actual with
  | exhausted =>
    exact ⟨actual, [], 0, .refl, represented, reads_nil data, Nat.le_refl _,
      fun seen => Shared.Requests.Visit.start .refl 0 (represented_key represented seen)⟩
  | @done fuel state next operation =>
    obtain ⟨final, events, cost, trace, finalRep, reads, _, bound⟩ :=
      worker_step model data actual side _ represented x valid
    rw [operation] at finalRep
    refine ⟨final, events, cost, trace, finalRep, reads, by simpa only [Nat.mul_one] using bound, ?_⟩
    intro seen
    rcases seen with before | after
    · exact Shared.Requests.Visit.start trace 0 (represented_key represented before)
    · have atEnd : (model.cursor side next).key? = some x := by simpa only [Seen, operation] using after
      exact Shared.Requests.Visit.finish trace 0 (represented_key finalRep atEnd)
  | more operation _ ih =>
    obtain ⟨middle, firstEvents, firstCost, first, middleRep, firstReads, _, firstBound⟩ :=
      worker_step model data actual side _ represented x valid
    rw [operation] at middleRep
    obtain ⟨final, lastEvents, lastCost, last, finalRep, lastReads, lastBound, visited⟩ := ih middle middleRep
    refine ⟨final, firstEvents ++ lastEvents, firstCost + lastCost, first.append last, finalRep,
      reads_append firstReads lastReads, by omega, ?_⟩
    intro seen
    simp only [Nat.add_comm 1, Seen, operation] at seen
    rcases seen with before | after
    · exact Shared.Requests.Visit.start (first.append last) 0 (represented_key represented before)
    · exact (visited after).prepend first

/-- Correct completed attempts both visit the request and reach another
certified boundary, without requiring completion at the visited node. -/
theorem completed {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (correct : Correct model) {side : Bool} {x fuel work : Nat}
    {state : σ} {result : Controller.Attempt σ}
    (run : Controller.AttemptRun worker side x fuel state result work) (done : result.done = true)
    (boundary : Boundary worker saved.size side state) (valid : x < saved.size)
    (data : Nat → Nat) (actual : Shared.State Nat 2) (represented : Represents model data actual side state) :
    ∃ final events cost, Shared.Requests.Visit actual final x events cost ∧
      Represents model data final side result.state ∧ Boundary worker saved.size side result.state ∧
      Reads data events ∧ cost ≤ 15 * work := by
  have access := run.to_access done
  obtain ⟨final, events, cost, _, finalRep, reads, bound, visited⟩ := attempt model run valid data actual represented
  exact ⟨final, events, cost, visited (correct side state x result.state work boundary valid access),
    finalRep, boundary.next valid access, reads, bound⟩

end RotationBST.Combo.Refinement.Visits
