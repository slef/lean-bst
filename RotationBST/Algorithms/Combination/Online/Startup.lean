module

public import RotationBST.Algorithms.Combination.Online.Correctness
public import RotationBST.Models.Pointer.Reshape
public import RotationBST.Algorithms.Combination.Analysis.Comparison
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Online

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}

theorem execute_append (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) (xs ys : List Nat) :
    execute p s (xs ++ ys) =
      let first := execute p s xs
      let rest := execute p first.1 ys
      (rest.1, first.2 + rest.2) := by
  induction xs generalizing s with
  | nil => simp [execute]
  | cons x xs ih => simp only [List.cons_append, execute, ih, Nat.add_assoc]

theorem execute_ready (p : Prepared model budget restore fields oldData)
    (s : State model p.data budget) (xs : List Nat) :
    execute p (some s) xs = (some (run p.contract s xs).1, (run p.contract s xs).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [execute, access, run, ih]

theorem execute_first (p : Prepared model budget restore fields oldData) (x : Nat) (xs : List Nat) :
    execute p none (x :: xs) =
      (some (run p.contract p.state (x :: xs)).1, p.cost + (run p.contract p.state (x :: xs)).2) := by
  simp only [execute, access, execute_ready, run, Nat.add_assoc]

/-- The fixed online policy serves every valid input from the original tree,
and its total charged preparation plus final potential has the same bound
as the earlier per-execution construction. -/
theorem execute_spec (p : Prepared model budget restore fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final work switches,
      Controller.Execution worker budget restore (Controller.initial worker budget) xs final work switches ∧
      Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
      (execute p none xs).2 ≤ 524 * p.saveCost + 8384 * work := by
  cases xs with
  | nil => exact ⟨Controller.initial worker budget, 0, 0, .nil, .nil, Nat.zero_le _⟩
  | cons x xs =>
    obtain ⟨work, switches, logical, physical, bound⟩ := run_spec p.contract p.state (x :: xs) valid
    rw [p.controller_initial] at logical
    refine ⟨_, work, switches, logical, ?_, ?_⟩
    · simpa only [execute_first, Prepared.current] using physical.prepend p.trace
    · have preparation := p.charged
      simp only [execute_first]
      omega

/-- One fixed online rule has the minimum-of-two prefix bound. All snapshot
and hand choices in `p` are made before the request sequence is quantified. -/
theorem minimum_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
      ((execute p none xs).2 : ℝ) ≤ 524 * (1088 * saved.size : ℝ) +
        8384 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  obtain ⟨final, work, switches, logical, physical, bound⟩ := execute_spec p xs valid
  have comparison := Analysis.minimum_bound well valid logical
  have charged : ((execute p none xs).2 : ℝ) ≤ 524 * (p.saveCost : ℝ) + 8384 * (work : ℝ) := by
    exact_mod_cast bound
  have setupBound : (p.saveCost : ℝ) ≤ 1088 * (saved.size : ℝ) := by exact_mod_cast p.saveBound
  exact ⟨physical, by nlinarith⟩

/-- A single prepared online policy works for every valid input prefix.
The well-behaved bounds select only the budget and fixed restore charge;
the smaller comparator is chosen in the proof, not by the request rule. -/
theorem prefix_policy (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∀ xs, (∀ x ∈ xs, x < saved.size) →
        Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
          ((execute p none xs).2 : ℝ) ≤ 524 * (1088 * saved.size : ℝ) + 8384 * (C₁ + 1 + 57 : Nat) *
            (2 * C₀ * min (Analysis.total charges false xs) (Analysis.total charges true xs) + 3 * overhead) := by
  have enough : C₁ * overhead ≤ Analysis.budget overhead C₁ := by
    simp only [Analysis.budget, Nat.add_mul, Nat.one_mul]; omega
  let p := prepare model correct (Analysis.budget overhead C₁) (57 * overhead)
    (well.fresh.mono enough) (by omega) nonempty fields oldData
  exact ⟨p, fun xs valid => minimum_bound well p xs valid⟩

end RotationBST.Combo.Online
