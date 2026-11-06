module

public import RotationBST.Algorithms.Combination.Analysis.Bounds
public import RotationBST.Algorithms.Combination.Analysis.Counting
public import RotationBST.Algorithms.Combination.Rounds.Certificates.Slices
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- The budget gap absorbs the additive well-behaved overhead of each closed
round. The remaining original-sequence charge pays one full overhead unit. -/
theorem closed_span_charge {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) xs final cost switches)
    (span : Rounds.Span)
    (member : span ∈ (Rounds.spans worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs).dropLast) :
    (overhead : ℝ) ≤ C₀ * span.charge (charges span.side xs) := by
  have bounds := Rounds.spans_bounds worker (budget overhead C₁) restore
    (Controller.initial worker (budget overhead C₁)) 0 xs span (List.mem_of_mem_dropLast member)
  obtain ⟨endState, work, complete, upper⟩ := well.segment_bound span.side xs valid span.start span.stop bounds.2.1
    (by simpa only [Nat.zero_add] using bounds.2.2)
  have lower := Rounds.Certificates.span_lower_bound execution span member endState work complete
  have lowerReal : (budget overhead C₁ : ℝ) < work := by exact_mod_cast lower
  simp only [budget, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at lowerReal
  change (overhead : ℝ) ≤ C₀ * mass charges span.side xs span.start span.stop
  nlinarith

/-- Disjoint same-worker closed spans pay for all their round overheads using
only the original sequence's charges. -/
theorem closed_count_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) (selected : Bool) :
    (Rounds.count selected (Rounds.spans worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs).dropLast : ℝ) * overhead ≤ C₀ * total charges selected xs := by
  let rounds := Rounds.spans worker (budget overhead C₁) restore (Controller.initial worker (budget overhead C₁)) 0 xs
  have lower : (Rounds.count selected rounds.dropLast : ℝ) * overhead ≤
      C₀ * Rounds.charge selected (charges selected xs) rounds.dropLast := by
    apply sum_span_bound
    intro span member same
    simpa only [same] using closed_span_charge well valid execution span member
  have separated : Rounds.Separated rounds.dropLast :=
    (Rounds.spans_separated worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs).sublist (List.dropLast_sublist rounds)
  have upper : Rounds.charge selected (charges selected xs) rounds.dropLast ≤ total charges selected xs := by
    apply Rounds.disjoint_charge (charges selected xs) (well.nonneg selected xs) _ 0 xs.length
      (Rounds.selected_separated selected rounds.dropLast separated)
    intro span member
    simpa only [Nat.zero_add] using Rounds.spans_bounds worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs span
      (List.mem_of_mem_dropLast (List.mem_of_mem_filter member))
  exact lower.trans (mul_le_mul_of_nonneg_left upper (Nat.cast_nonneg C₀))

/-- Whole-prefix comparison against either worker, with a uniform explicit
constant. Restore cost is bounded here by the charged `restoreFactor * overhead`. -/
theorem prefix_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 3 * overhead) := by
  let rounds := Rounds.spans worker (budget overhead C₁) (restoreFactor * overhead)
    (Controller.initial worker (budget overhead C₁)) 0 xs
  let k := Rounds.count selected rounds.dropLast
  have paid := closed_count_bound well valid execution selected
  change (k : ℝ) * overhead ≤ C₀ * total charges selected xs at paid
  have countBound : Rounds.count selected rounds ≤ k + 1 := count_dropLast selected rounds
  have operational := Rounds.work_by_rounds execution (by simp [Controller.initial]) 0 selected
  have integerBound : cost ≤ (2 * k + 3) * (budget overhead C₁ + restoreFactor * overhead) :=
    operational.trans (Nat.mul_le_mul_right _ (by change 2 * Rounds.count selected rounds + 1 ≤ 2 * k + 3; omega))
  have realBound : (cost : ℝ) ≤ (2 * (k : ℝ) + 3) * ((budget overhead C₁ : ℝ) + restoreFactor * overhead) := by
    exact_mod_cast integerBound
  calc
    (cost : ℝ) ≤ (2 * (k : ℝ) + 3) * ((budget overhead C₁ : ℝ) + restoreFactor * overhead) := realBound
    _ = (C₁ + 1 + restoreFactor : Nat) * (2 * ((k : ℝ) * overhead) + 3 * overhead) := by
      simp only [budget, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    _ ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 3 * overhead) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (C₁ + 1 + restoreFactor))
      nlinarith only [paid]

end RotationBST.Combo.Analysis
