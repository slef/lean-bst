module

public import RotationBST.Algorithms.Combination.Analysis.Amortized
public import RotationBST.Algorithms.Combination.Rounds.Certificates.Interior
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- Interior closed rounds pay their overhead even when the controller state
at the start of the measured window did not come from a fresh restart. -/
theorem interior_span_charge {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore s xs t cost switches)
    (span : Rounds.Span)
    (member : span ∈ (Rounds.spans worker (budget overhead C₁) restore s 0 xs).dropLast.tail) :
    (overhead : ℝ) ≤ C₀ * span.charge (charges span.side xs) := by
  have bounds := Rounds.spans_bounds worker (budget overhead C₁) restore s 0 xs span
    (List.mem_of_mem_dropLast (List.mem_of_mem_tail member))
  obtain ⟨endState, work, complete, upper⟩ := well.segment_bound span.side xs valid span.start span.stop bounds.2.1
    (by simpa only [Nat.zero_add] using bounds.2.2)
  have lower := (Rounds.Certificates.interior_spans execution span member).lower_bound complete
  have lowerReal : (budget overhead C₁ : ℝ) < work := by exact_mod_cast lower
  simp only [budget, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at lowerReal
  change (overhead : ℝ) ≤ C₀ * mass charges span.side xs span.start span.stop
  nlinarith

/-- The number of selected interior rounds is paid by the window's charges. -/
theorem interior_count_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore s xs t cost switches) (selected : Bool) :
    (Rounds.count selected (Rounds.spans worker (budget overhead C₁) restore s 0 xs).dropLast.tail : ℝ) * overhead ≤
      C₀ * total charges selected xs := by
  let rounds := Rounds.spans worker (budget overhead C₁) restore s 0 xs
  have lower : (Rounds.count selected rounds.dropLast.tail : ℝ) * overhead ≤
      C₀ * Rounds.charge selected (charges selected xs) rounds.dropLast.tail := by
    apply sum_span_bound
    intro span member same
    simpa only [same] using interior_span_charge well valid execution span member
  have separated : Rounds.Separated rounds.dropLast.tail :=
    ((Rounds.spans_separated worker (budget overhead C₁) restore s 0 xs).sublist
      (List.dropLast_sublist rounds)).sublist (List.tail_sublist rounds.dropLast)
  have upper : Rounds.charge selected (charges selected xs) rounds.dropLast.tail ≤ total charges selected xs := by
    apply Rounds.disjoint_charge (charges selected xs) (well.nonneg selected xs) _ 0 xs.length
      (Rounds.selected_separated selected rounds.dropLast.tail separated)
    intro span member
    simpa only [Nat.zero_add] using Rounds.spans_bounds worker (budget overhead C₁) restore s 0 xs span
      (List.mem_of_mem_dropLast (List.mem_of_mem_tail (List.mem_of_mem_filter member)))
  exact lower.trans (mul_le_mul_of_nonneg_left upper (Nat.cast_nonneg C₀))

/-- A comparison from any bounded controller state. Losing the initial and
final boundary rounds costs only two extra overhead units in the coefficient. -/
theorem state_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead) s xs t cost switches)
    (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 5 * overhead) := by
  let rounds := Rounds.spans worker (budget overhead C₁) (restoreFactor * overhead) s 0 xs
  let k := Rounds.count selected rounds.dropLast.tail
  have paid := interior_count_bound well valid execution selected
  change (k : ℝ) * overhead ≤ C₀ * total charges selected xs at paid
  have dropBound := count_dropLast selected rounds
  have tailBound := count_tail selected rounds.dropLast
  have operational := Rounds.work_by_rounds execution limit 0 selected
  have integerBound : cost ≤ (2 * k + 5) * (budget overhead C₁ + restoreFactor * overhead) :=
    operational.trans (Nat.mul_le_mul_right _ (by change 2 * Rounds.count selected rounds + 1 ≤ 2 * k + 5; omega))
  have realBound : (cost : ℝ) ≤ (2 * (k : ℝ) + 5) * ((budget overhead C₁ : ℝ) + restoreFactor * overhead) := by
    exact_mod_cast integerBound
  calc
    (cost : ℝ) ≤ (2 * (k : ℝ) + 5) * ((budget overhead C₁ : ℝ) + restoreFactor * overhead) := realBound
    _ = (C₁ + 1 + restoreFactor : Nat) * (2 * ((k : ℝ) * overhead) + 5 * overhead) := by
      simp only [budget, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring
    _ ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 5 * overhead) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (C₁ + 1 + restoreFactor))
      nlinarith only [paid]

/-- The measured segment can be compared with charges in the original input,
without restarting the controller at its left endpoint. Applying stability
once more gives uniform constants independent of the segment endpoints. -/
theorem window_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {lo hi cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n) (ordered : lo ≤ hi) (inside : hi ≤ xs.length)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      s (segment xs lo hi) t cost switches) (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * C₀ * mass charges selected xs lo hi + (2 * C₀ * C₁ + 5) * overhead) := by
  have localBound := state_bound well limit (segment_valid valid lo hi) execution selected
  have stable := well.stable selected xs valid lo hi ordered inside
  have nonneg : (0 : ℝ) ≤ overhead := Nat.cast_nonneg _
  have compare : total charges selected (segment xs lo hi) ≤ C₀ * mass charges selected xs lo hi + C₁ * overhead := by
    linarith
  have paid := mul_le_mul_of_nonneg_left compare (show (0 : ℝ) ≤ 2 * C₀ by positivity)
  apply localBound.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg (C₁ + 1 + restoreFactor))
  nlinarith only [paid]

/-- The same continuing controller run satisfies both window comparisons. -/
theorem window_minimum {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {lo hi cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n) (ordered : lo ≤ hi) (inside : hi ≤ xs.length)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      s (segment xs lo hi) t cost switches) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * C₀ * min (mass charges false xs lo hi) (mass charges true xs lo hi) + (2 * C₀ * C₁ + 5) * overhead) := by
  by_cases smaller : mass charges false xs lo hi ≤ mass charges true xs lo hi
  · simpa only [min_eq_left smaller] using window_bound well limit valid ordered inside execution false
  · simpa only [min_eq_right (le_of_not_ge smaller)] using window_bound well limit valid ordered inside execution true

end RotationBST.Combo.Analysis
