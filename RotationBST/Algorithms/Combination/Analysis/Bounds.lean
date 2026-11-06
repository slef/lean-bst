module

public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Attempts
public import RotationBST.Algorithms.Combination.Controller.Progress
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Analysis

theorem segment_valid {n : Nat} {xs : List Nat} (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) :
    ∀ x ∈ segment xs lo hi, x < n := by
  intro x member
  exact valid x (List.mem_of_mem_drop (List.mem_of_mem_take member))

/-- The full single-access hypothesis supplies the controller's fresh-round
progress condition, with its exact normalized request cost. -/
theorem WellBehaved.fresh {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) : Controller.FreshBound worker n (C₁ * overhead) := by
  intro side x valid
  obtain ⟨final, cost, access, bound⟩ := well.single side [] (worker.restart side) 0 .nil (by simp) x valid
  have computed := Controller.AttemptRun.computed access
  have done : (Controller.attempt worker side x cost (worker.restart side)).done = true := by rw [computed]
  have extra := Controller.attempt_extra worker side x cost (C₁ * overhead - cost) (worker.restart side) done
  rw [Nat.add_sub_of_le bound] at extra
  rw [extra]
  exact done

/-- A contiguous segment has a completed standalone worker execution bounded
by its original-sequence charges and the well-behaved overhead. -/
theorem WellBehaved.segment_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) (side : Bool) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    ∃ final cost, Worker.Requests worker side (worker.restart side) (segment xs lo hi) final cost ∧
      (cost : ℝ) ≤ C₀ * mass charges side xs lo hi + C₁ * overhead := by
  obtain ⟨final, cost, run, bound⟩ := well.upper side (segment xs lo hi) (segment_valid valid lo hi)
  exact ⟨final, cost, run, bound.trans (well.stable side xs valid lo hi ordered inside)⟩

end RotationBST.Combo.Analysis
