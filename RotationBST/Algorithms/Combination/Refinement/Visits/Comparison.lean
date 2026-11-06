module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Execution
public import RotationBST.Structures.TreeBuffer.Shared.Erasure.Traces
public import RotationBST.Algorithms.Combination.Analysis.Comparison
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Refinement.Visits
open TreeBuffer
open Snapshot.Streaming.Refinement (Reads)

/-- Correct requests survive both the shared-node implementation and erasure
to the library's existing persistent multifinger request model. -/
theorem multifinger {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (correct : Correct model)
    {budget restore : Nat} {s t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker budget restore s xs t work switches)
    (boundary : Boundary worker saved.size s.side s.workerState) (valid : ∀ x ∈ xs, x < saved.size)
    (paid : 841 * saved.size ≤ 15 * restore) (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual s.side s.workerState) :
    ∃ final events physicalCost pointerCost,
      Shared.Requests.Execution actual xs final events physicalCost ∧
      Multifinger.Execution actual.erase xs final.erase pointerCost ∧
      Represents model data final t.side t.workerState ∧ Reads data events ∧
      pointerCost ≤ physicalCost ∧ physicalCost ≤ 16 * work := by
  obtain ⟨final, events, cost, served, finalRep, _, reads, bound⟩ :=
    execution model correct run boundary valid paid data stored actual represented
  obtain ⟨pointerCost, erased, charged⟩ := served.erase data represented.2.1
  exact ⟨final, events, cost, pointerCost, served, erased, finalRep, reads, charged, bound⟩

/-- The whole-prefix bound now applies to actual request-serving executions,
including one unit per request, rather than only to unmarked instruction traces. -/
theorem prefix_bound {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (correct : Correct model)
    {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    {t : Controller.State σ} {xs : List Nat} {work switches : Nat}
    (run : Controller.Execution worker (Analysis.budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (Analysis.budget overhead C₁)) xs t work switches)
    (valid : ∀ x ∈ xs, x < saved.size) (paid : 841 * saved.size ≤ 15 * (restoreFactor * overhead))
    (data : Nat → Nat) (stored : Snapshot.CellIO.Stored saved data)
    (actual : Shared.State Nat 2) (represented : Represents model data actual false (worker.restart false)) :
    ∃ final events physicalCost pointerCost,
      Shared.Requests.Execution actual xs final events physicalCost ∧
      Multifinger.Execution actual.erase xs final.erase pointerCost ∧
      Represents model data final t.side t.workerState ∧ Reads data events ∧ pointerCost ≤ physicalCost ∧
      (physicalCost : ℝ) ≤ 16 * (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  obtain ⟨final, events, physicalCost, pointerCost, served, erased, finalRep, reads, charged, bound⟩ :=
    multifinger model correct run (boundary_restart worker saved.size false) valid paid data stored actual represented
  have comparison := Analysis.minimum_bound well valid run
  have realBound : (physicalCost : ℝ) ≤ 16 * (work : ℝ) := by exact_mod_cast bound
  refine ⟨final, events, physicalCost, pointerCost, served, erased, finalRep, reads, charged, realBound.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left comparison (by norm_num : (0 : ℝ) ≤ 16)

end RotationBST.Combo.Refinement.Visits
