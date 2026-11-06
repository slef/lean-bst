module

public import RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Steps

@[expose] public section
namespace RotationBST.Combo.Refinement
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads reads_nil reads_one reads_append)

/-- A causal worker step acts on the shared tree with at most fifteen units,
including rotation metadata. Cursor-preserving bookkeeping is represented by
a charged read; the stored snapshot and inactive buffer finger are preserved. -/
theorem worker_step {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (data : Nat → Nat) (actual : Shared.State Nat 2)
    (side : Bool) (state : σ) (represented : Represents model data actual side state)
    (x : Nat) (valid : x < saved.size) :
    ∃ final events cost, Shared.Trace actual final events cost ∧
      Represents model data final side (worker.step side state x).1 ∧ Reads data events ∧
      final.position 1 = actual.position 1 ∧ cost ≤ 15 := by
  have ready := model.step_ready side state x represented.1 valid
  have operation := model.step_cursor side state x represented.1 valid
  cases chosen : model.instruction side state x with
  | none =>
    simp only [chosen] at operation
    have action := Shared.read_exists actual data represented.2.1 0
    refine ⟨actual, [.read (actual.position 0) (data (actual.position 0))], 1, action.trace,
      ⟨ready, represented.2.1, ?_, ?_⟩, reads_one data _, rfl, by decide⟩
    · simpa only [operation] using represented.2.2.1
    · simpa only [operation] using represented.2.2.2
  | some op =>
    simp only [chosen] at operation
    obtain ⟨nextKey, atNext⟩ := (Multifinger.perform_sound operation).keys_exist.2
    obtain ⟨final, cost, action, bound, shape, positions⟩ :=
      Shared.execute_exists actual data represented.2.1 0 op _ _ represented.2.2.1.symm represented.2.2.2
        operation nextKey atNext
    refine ⟨final, [], cost, action.trace,
      ⟨ready, action.valid data represented.2.1, shape, ?_⟩, reads_nil data, ?_, bound⟩
    · simpa only [positions, Function.update_self] using atNext
    · simp only [positions, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

/-- Every finite attempted request, including an exhausted partial request,
has a charged shared-node realization. The physical trace is linear in the
actual worker steps consumed, not in the supplied fuel. -/
theorem attempt {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) {side : Bool} {x fuel work : Nat} {state : σ} {result : Controller.Attempt σ}
    (run : Controller.AttemptRun worker side x fuel state result work) (valid : x < saved.size)
    (data : Nat → Nat) (actual : Shared.State Nat 2) (represented : Represents model data actual side state) :
    ∃ final events cost, Shared.Trace actual final events cost ∧ Represents model data final side result.state ∧
      Reads data events ∧ final.position 1 = actual.position 1 ∧ cost ≤ 15 * work := by
  induction run generalizing actual with
  | exhausted => exact ⟨actual, [], 0, .refl, represented, reads_nil data, rfl, Nat.le_refl _⟩
  | done operation =>
    simpa only [operation, Nat.mul_one] using worker_step model data actual side _ represented x valid
  | more operation _ ih =>
    obtain ⟨middle, firstEvents, firstCost, first, middleRep, firstReads, firstPosition, firstBound⟩ :=
      worker_step model data actual side _ represented x valid
    rw [operation] at middleRep
    obtain ⟨final, lastEvents, lastCost, last, finalRep, lastReads, lastPosition, lastBound⟩ := ih middle middleRep
    exact ⟨final, firstEvents ++ lastEvents, firstCost + lastCost, first.append last, finalRep,
      reads_append firstReads lastReads, lastPosition.trans firstPosition, by omega⟩

end RotationBST.Combo.Refinement
