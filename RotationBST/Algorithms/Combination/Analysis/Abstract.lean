module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Analysis.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Analysis.Results

theorem fresh {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) : Controller.FreshBound worker n (C₁ * overhead) :=
  RotationBST.Combo.Analysis.WellBehaved.fresh well

theorem segment_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) (side : Bool) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    ∃ final cost, Worker.Requests worker side (worker.restart side) (segment xs lo hi) final cost ∧
      (cost : ℝ) ≤ C₀ * mass charges side xs lo hi + C₁ * overhead :=
  RotationBST.Combo.Analysis.WellBehaved.segment_bound well side xs valid lo hi ordered inside

theorem closed_span_charge {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) xs final cost switches)
    (span : Rounds.Span)
    (member : span ∈ (Rounds.spans worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs).dropLast) :
    (overhead : ℝ) ≤ C₀ * span.charge (charges span.side xs) :=
  RotationBST.Combo.Analysis.closed_span_charge well valid execution span member

theorem closed_count_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) (selected : Bool) :
    (Rounds.count selected (Rounds.spans worker (budget overhead C₁) restore
      (Controller.initial worker (budget overhead C₁)) 0 xs).dropLast : ℝ) * overhead ≤ C₀ * total charges selected xs :=
  RotationBST.Combo.Analysis.closed_count_bound well valid execution selected

theorem prefix_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 3 * overhead) :=
  RotationBST.Combo.Analysis.prefix_bound well valid execution selected

theorem minimum_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      (Controller.initial worker (budget overhead C₁)) xs final cost switches) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * min (total charges false xs) (total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Analysis.minimum_bound well valid execution

theorem execute {σ : Type} (worker : Controller.Worker σ) (n overhead C₀ C₁ restoreFactor : Nat) (charges : Charges)
    (well : WellBehaved worker n overhead C₀ C₁ charges) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ final cost switches,
      Controller.run worker (budget overhead C₁) (restoreFactor * overhead)
        (Controller.initial worker (budget overhead C₁)) xs = some (final, cost) ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        (Controller.initial worker (budget overhead C₁)) xs final cost switches ∧
      (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * min (total charges false xs) (total charges true xs) + 3 * overhead) :=
  RotationBST.Combo.Analysis.execute worker n overhead C₀ C₁ restoreFactor charges well xs valid

theorem interior_span_charge {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore s xs t cost switches)
    (span : Rounds.Span)
    (member : span ∈ (Rounds.spans worker (budget overhead C₁) restore s 0 xs).dropLast.tail) :
    (overhead : ℝ) ≤ C₀ * span.charge (charges span.side xs) :=
  RotationBST.Combo.Analysis.interior_span_charge well valid execution span member

theorem interior_count_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restore : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) restore s xs t cost switches) (selected : Bool) :
    (Rounds.count selected (Rounds.spans worker (budget overhead C₁) restore s 0 xs).dropLast.tail : ℝ) * overhead ≤
      C₀ * total charges selected xs :=
  RotationBST.Combo.Analysis.interior_count_bound well valid execution selected

theorem state_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead) s xs t cost switches)
    (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) * (2 * C₀ * total charges selected xs + 5 * overhead) :=
  RotationBST.Combo.Analysis.state_bound well limit valid execution selected

theorem window_bound {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {lo hi cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n) (ordered : lo ≤ hi) (inside : hi ≤ xs.length)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      s (segment xs lo hi) t cost switches) (selected : Bool) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * C₀ * mass charges selected xs lo hi + (2 * C₀ * C₁ + 5) * overhead) :=
  RotationBST.Combo.Analysis.window_bound well limit valid ordered inside execution selected

theorem window_minimum {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {lo hi cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n) (ordered : lo ≤ hi) (inside : hi ≤ xs.length)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
      s (segment xs lo hi) t cost switches) :
    (cost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
      (2 * C₀ * C₀ * min (mass charges false xs lo hi) (mass charges true xs lo hi) + (2 * C₀ * C₁ + 5) * overhead) :=
  RotationBST.Combo.Analysis.window_minimum well limit valid ordered inside execution

theorem executed_window {σ : Type} {worker : Controller.Worker σ} {n overhead C₀ C₁ restoreFactor : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges) {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (limit : s.left ≤ budget overhead C₁) (valid : ∀ x ∈ xs, x < n)
    (execution : Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead) s xs t cost switches)
    (lo hi : Nat) (ordered : lo ≤ hi) (inside : hi ≤ xs.length) :
    ∃ beforeState afterState beforeCost windowCost afterCost beforeSwitches windowSwitches afterSwitches,
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        s (xs.take lo) beforeState beforeCost beforeSwitches ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        beforeState (segment xs lo hi) afterState windowCost windowSwitches ∧
      Controller.Execution worker (budget overhead C₁) (restoreFactor * overhead)
        afterState (xs.drop hi) t afterCost afterSwitches ∧
      cost = beforeCost + windowCost + afterCost ∧ switches = beforeSwitches + windowSwitches + afterSwitches ∧
      (windowCost : ℝ) ≤ (C₁ + 1 + restoreFactor : Nat) *
        (2 * C₀ * C₀ * min (mass charges false xs lo hi) (mass charges true xs lo hi) + (2 * C₀ * C₁ + 5) * overhead) :=
  RotationBST.Combo.Analysis.executed_window well limit valid execution lo hi ordered inside

theorem overhead_mono {σ : Type} {worker : Controller.Worker σ}
    {n overhead larger C₀ C₁ : Nat} {charges : Charges}
    (well : WellBehaved worker n overhead C₀ C₁ charges)
    (increased : overhead ≤ larger) (constant : 1 ≤ C₁) :
    WellBehaved worker n larger C₀ C₁ charges :=
  well.overhead_mono increased constant

end RotationBST.Combo.Analysis.Results

/-- info: abstract audit passed for `RotationBST.Combo.Analysis.Results`: 14 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Analysis.Results allowing [
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract]
