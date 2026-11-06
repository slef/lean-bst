module

public import RotationBST.Algorithms.Combination.Refinement.Execution
public import RotationBST.Algorithms.Combination.Analysis.Comparison
public import RotationBST.Structures.TreeBuffer.Snapshot.Startup.Operations
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Refinement
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads)

/-- Transfer the minimum-of-two bound to the shared-node instruction trace,
assuming a saved snapshot already exists. The worker model is an explicit
local instruction contract, not an assumption of the resulting cost theorem. -/
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
        (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  obtain ⟨final, events, cost, trace, finalRep, reads, charged⟩ :=
    execution model run valid paid data stored actual represented
  have comparison := Analysis.minimum_bound well valid run
  have chargedReal : (cost : ℝ) ≤ 15 * (work : ℝ) := by exact_mod_cast charged
  refine ⟨final, events, cost, trace, finalRep, reads, chargedReal.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left comparison (by norm_num : (0 : ℝ) ≤ 15)

/-- Initialize the node fields, save the initial tree, and run the same causal
controller with real shared-node restores. The conventional `n ≤ F` assumption
makes a logical restore charge `57F` cover the `841n` implementation under the
factor-fifteen instruction simulation. Startup contributes at most `1088n`.
Request visitation and finite-address implementation remain separate contracts. -/
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
        (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  obtain ⟨ready, snapshotData, saveEvents, saveCost, setup, readyValid, stored, shape, atRoot, setupBound⟩ :=
    Snapshot.Startup.save saved saved.size rfl nonempty fields data
  have represented : Represents model snapshotData ready false (worker.restart false) :=
    ⟨model.restart_ready false, readyValid,
      by simpa only [model.restart_cursor, Pointer.Config.tree, Pointer.plug] using shape,
      by simpa only [model.restart_cursor] using atRoot⟩
  obtain ⟨endState, work, switches, computed, run, _⟩ :=
    Analysis.execute worker saved.size overhead C₀ C₁ 57 charges well xs valid
  obtain ⟨final, events, cost, trace, finalRep, reads, bound⟩ :=
    execution_bound model well run valid (by omega) snapshotData stored ready represented
  refine ⟨ready, snapshotData, saveEvents, saveCost, final, events, cost, endState, work, switches,
    setup, stored, computed, run, trace, finalRep, reads, ?_⟩
  have setupReal : (saveCost : ℝ) ≤ 1088 * (saved.size : ℝ) := by exact_mod_cast setupBound
  simpa only [Nat.cast_add] using add_le_add setupReal bound

end RotationBST.Combo.Refinement
