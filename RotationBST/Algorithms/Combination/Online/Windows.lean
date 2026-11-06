module

public import RotationBST.Algorithms.Combination.Online.Startup
public import RotationBST.Algorithms.Combination.Analysis.Windows
public import RotationBST.Structures.FingerHand.Packed.Potential
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Online

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget restore : Nat}
  {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}

theorem State.potential (s : State model data budget) : s.hand.potential ≤ 32 * saved.size := by
  have bound := s.handRep.potential
  have shape := s.represented.2.2.1
  have size := model.size s.controller.side s.controller.workerState s.represented.1
  change s.hand.potential ≤ 32 * s.actual.tree.erase.size at bound
  simpa only [shape, size] using bound

theorem Prepared.left_le (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) : (p.controller s).left ≤ budget := by
  cases s with
  | none => exact Nat.le_refl _
  | some ready => exact ready.left_le

/-- Continue from the actual optional policy state. An initialized hand pays
at most `32n` in carried potential; a fresh state pays at most `524 * 1088n`
for preparation. The latter is a uniform bound covering both cases. -/
theorem execute_from (p : Prepared model budget restore fields oldData)
    (s : Option (State model p.data budget)) (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ final work switches,
      Controller.Execution worker budget restore (p.controller s) xs final work switches ∧
      Pointer.Execution (p.current s) xs (p.current (execute p s xs).1) (execute p s xs).2 ∧
      (execute p s xs).2 ≤ 570112 * saved.size + 8384 * work := by
  cases s with
  | none =>
    obtain ⟨final, work, switches, logical, physical, charged⟩ := execute_spec p xs valid
    have startup := p.saveBound
    exact ⟨final, work, switches, logical, physical, by omega⟩
  | some ready =>
    obtain ⟨work, switches, logical, physical, charged⟩ := run_spec p.contract ready xs valid
    have potential := ready.potential
    refine ⟨_, work, switches, logical, ?_, ?_⟩
    · simpa only [execute_ready, Prepared.current] using physical
    · simp only [execute_ready]
      omega

/-- A physical continuation on the measured segment is compared with that
segment's charges in the original sequence. Neither the controller nor the
hand is reinitialized at the left endpoint. -/
theorem window_bound {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (s : Option (State model p.data (Analysis.budget overhead C₁)))
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    Pointer.Execution (p.current s) (Analysis.segment xs lo hi)
        (p.current (execute p s (Analysis.segment xs lo hi)).1) (execute p s (Analysis.segment xs lo hi)).2 ∧
      ((execute p s (Analysis.segment xs lo hi)).2 : ℝ) ≤ 570112 * (saved.size : ℝ) +
        8384 * (C₁ + 1 + restoreFactor : Nat) *
          (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
            (2 * C₀ * C₁ + 5) * overhead) := by
  obtain ⟨final, work, switches, logical, physical, bound⟩ :=
    execute_from p s (Analysis.segment xs lo hi) (Analysis.segment_valid valid lo hi)
  have comparison := Analysis.window_minimum well (p.left_le s) valid ordered inside logical
  have charged : ((execute p s (Analysis.segment xs lo hi)).2 : ℝ) ≤
      570112 * (saved.size : ℝ) + 8384 * (work : ℝ) := by exact_mod_cast bound
  exact ⟨physical, by nlinarith⟩

/-- Exact three-way splitting of the fixed policy, including all physical
states and charges. The middle cost is part of the original run. -/
theorem execute_window_split (p : Prepared model budget restore fields oldData)
    (xs : List Nat) (lo hi : Nat) (ordered : lo ≤ hi) :
    let first := execute p none (xs.take lo)
    let middle := execute p first.1 (Analysis.segment xs lo hi)
    let last := execute p middle.1 (xs.drop hi)
    execute p none xs = (last.1, first.2 + middle.2 + last.2) := by
  have partition : (xs.take lo ++ Analysis.segment xs lo hi) ++ xs.drop hi = xs := by
    have drop : (xs.drop lo).drop (hi - lo) = xs.drop hi := by
      rw [List.drop_drop, Nat.add_sub_of_le ordered]
    rw [Analysis.segment, List.append_assoc, ← drop, List.take_append_drop, List.take_append_drop]
  dsimp only
  calc
    execute p none xs = execute p none ((xs.take lo ++ Analysis.segment xs lo hi) ++ xs.drop hi) :=
      congrArg (execute p none) partition.symm
    _ = _ := by simp only [execute_append]

/-- Every window of one fixed physical run has the minimum-of-two bound,
with the actual boundary trees and the exact additive cost decomposition. -/
theorem executed_window {overhead C₀ C₁ restoreFactor : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (p : Prepared model (Analysis.budget overhead C₁) (restoreFactor * overhead) fields oldData)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) (lo hi : Nat)
    (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    let first := execute p none (xs.take lo)
    let middle := execute p first.1 (Analysis.segment xs lo hi)
    let last := execute p middle.1 (xs.drop hi)
    execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
      Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
      (middle.2 : ℝ) ≤ 570112 * (saved.size : ℝ) + 8384 * (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
          (2 * C₀ * C₁ + 5) * overhead) := by
  exact ⟨execute_window_split p xs lo hi ordered,
    window_bound well p (execute p none (xs.take lo)).1 xs valid lo hi ordered inside⟩

/-- The abstract online combination theorem for actual contiguous-window
costs. One policy is fixed before all input sequences and window endpoints.
The `n ≤ F` hypothesis absorbs preparation and carried potential into `F`. -/
theorem window_policy (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    {overhead C₀ C₁ : Nat} {charges : Analysis.Charges}
    (well : Analysis.WellBehaved worker saved.size overhead C₀ C₁ charges)
    (nonempty : saved ≠ .nil) (size : saved.size ≤ overhead)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    ∃ p : Prepared model (Analysis.budget overhead C₁) (57 * overhead) fields oldData,
      ∀ xs, (∀ x ∈ xs, x < saved.size) →
        Pointer.Execution saved xs (p.current (execute p none xs).1) (execute p none xs).2 ∧
        ∀ lo hi, lo ≤ hi → hi ≤ xs.length →
          let first := execute p none (xs.take lo)
          let middle := execute p first.1 (Analysis.segment xs lo hi)
          let last := execute p middle.1 (xs.drop hi)
          execute p none xs = (last.1, first.2 + middle.2 + last.2) ∧
            Pointer.Execution (p.current first.1) (Analysis.segment xs lo hi) (p.current middle.1) middle.2 ∧
            (middle.2 : ℝ) ≤ 8384 * (C₁ + 1 + 57 : Nat) *
              (2 * C₀ * C₀ * min (Analysis.mass charges false xs lo hi) (Analysis.mass charges true xs lo hi) +
                (2 * C₀ * C₁ + 73) * overhead) := by
  obtain ⟨p, prefixes⟩ := prefix_policy model correct well nonempty size fields oldData
  refine ⟨p, ?_⟩
  intro xs valid
  refine ⟨(prefixes xs valid).1, ?_⟩
  intro lo hi ordered inside
  obtain ⟨split, physical, bound⟩ := executed_window well p xs valid lo hi ordered inside
  refine ⟨split, physical, ?_⟩
  have sizeReal : (saved.size : ℝ) ≤ overhead := by exact_mod_cast size
  have factor : (1 : ℝ) ≤ (C₁ + 1 + 57 : Nat) := by exact_mod_cast (show 1 ≤ C₁ + 1 + 57 by omega)
  have scaled := mul_le_mul_of_nonneg_right factor (Nat.cast_nonneg overhead)
  nlinarith

end RotationBST.Combo.Online
