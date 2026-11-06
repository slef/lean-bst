module

public import RotationBST.Algorithms.Combination.Online.Replay.Preparation
public import RotationBST.Algorithms.Combination.Controller.Progress
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Online.Replay

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}

theorem source_single (p : Prepared model budget restore fields oldData)
    (s : Option (Online.State model p.data budget)) (x : Nat) (valid : x < saved.size) :
    (access p s x).2 ≤ 570112 * saved.size + 8384 * (2 * budget + restore) := by
  obtain ⟨_, _, _, logical, _, charged⟩ := Online.Results.execute_from p s [x]
    (by intro y member; simp only [List.mem_singleton] at member; subst y; exact valid)
  cases logical with
  | cons done rest =>
    cases rest
    have bound := Controller.serve_work_bound worker budget restore (p.controller s) x (Online.Results.remaining_budget p s)
    simp only [execute, Nat.add_zero] at charged
    omega

theorem single (p : Prepared model budget restore fields oldData) (implementation : Implementation p)
    (side : Bool) (state : Worker.Replay.State (Option (Online.State model p.data budget))) (x : Nat)
    (boundary : Refinement.Visits.Boundary (Worker.Replay.worker implementation.planner) saved.size side state)
    (valid : x < saved.size) :
    ∃ final cost, Worker.Access (Worker.Replay.worker implementation.planner) side state x final cost ∧
      cost ≤ 1140224 * saved.size + 16768 * (2 * budget + restore) := by
  obtain ⟨original, rfl, size⟩ := Worker.Replay.Results.request_boundary implementation.planner boundary
  have ran := Worker.Replay.Results.access implementation.planner side original x size valid
  have expanded := (implementation.expansion side original x valid).2
  have source := source_single p original x valid
  exact ⟨_, _, ran, by omega⟩

theorem minimum_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (implementation : Implementation p) (side : Bool) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ cost, Worker.Requests (Worker.Replay.worker implementation.planner) side
      ((Worker.Replay.worker implementation.planner).restart side) xs
      (.boundary (execute p none xs).1) cost ∧
      (cost : ℝ) ≤ 1140224 * (saved.size : ℝ) +
        16768 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  obtain ⟨cost, ran, bound⟩ := requests p implementation side xs valid
  have source := (Online.Results.minimum_bound well p xs valid).2
  have expanded : (cost : ℝ) ≤ 2 * (execute p none xs).2 := by exact_mod_cast bound
  exact ⟨cost, ran, by nlinarith only [expanded, source]⟩

theorem scaled_mass (factor : Nat) (charges : Analysis.Charges) (side : Bool) (xs : List Nat) (lo hi : Nat) :
    Analysis.mass (scaledCharges factor charges) side xs lo hi = factor * Analysis.mass charges side xs lo hi := by
  simp only [Analysis.mass, scaledCharges, Finset.mul_sum]

theorem scaled_total (factor : Nat) (charges : Analysis.Charges) (side : Bool) (xs : List Nat) :
    Analysis.total (scaledCharges factor charges) side xs = factor * Analysis.total charges side xs :=
  scaled_mass factor charges side xs 0 xs.length

theorem factor_bounds (C₀ C₁ restoreFactor : Nat) :
    chargeFactor C₀ C₁ restoreFactor ≤ overheadFactor C₀ C₁ restoreFactor ∧
    16768 * (68 + 3 * (C₁ + 1 + restoreFactor)) ≤ overheadFactor C₀ C₁ restoreFactor ∧
    16768 * (68 + 2 * (C₁ + 1) + restoreFactor) ≤ overheadFactor C₀ C₁ restoreFactor := by
  simp only [overheadFactor, Nat.mul_add]
  omega

end RotationBST.Combo.Online.Replay
