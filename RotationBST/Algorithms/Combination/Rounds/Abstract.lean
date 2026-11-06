module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Rounds.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Rounds.Results

theorem cuts_ordered {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    (cuts worker budget restore s offset xs).Pairwise (· < ·) ∧
      ∀ i ∈ cuts worker budget restore s offset xs, offset ≤ i ∧ i < offset + xs.length :=
  RotationBST.Combo.Rounds.cuts_ordered worker budget restore s offset xs

theorem cuts_length {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) :
    (cuts worker budget restore s offset xs).length = switches :=
  RotationBST.Combo.Rounds.cuts_length execution offset

theorem spans_bounds {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    ∀ span ∈ spans worker budget restore s offset xs,
      offset ≤ span.start ∧ span.start ≤ span.stop ∧ span.stop ≤ offset + xs.length :=
  RotationBST.Combo.Rounds.spans_bounds worker budget restore s offset xs

theorem spans_separated {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    Separated (spans worker budget restore s offset xs) :=
  RotationBST.Combo.Rounds.spans_separated worker budget restore s offset xs

theorem spans_length {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) :
    (spans worker budget restore s offset xs).length = switches + 1 :=
  RotationBST.Combo.Rounds.spans_length execution offset

theorem rounds_count {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) (selected : Bool) :
    switches + 1 ≤ 2 * count selected (spans worker budget restore s offset xs) + 1 :=
  RotationBST.Combo.Rounds.rounds_count execution offset selected

theorem work_by_rounds {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (limit : s.left ≤ budget)
    (offset : Nat) (selected : Bool) :
    cost ≤ (2 * count selected (spans worker budget restore s offset xs) + 1) * (budget + restore) :=
  RotationBST.Combo.Rounds.work_by_rounds execution limit offset selected

theorem charge_le_interval {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (selected : Bool)
    (weights : Nat → ℝ) (nonneg : ∀ i, 0 ≤ weights i) :
    charge selected weights (spans worker budget restore s offset xs) ≤
      ∑ i ∈ Finset.Ico offset (offset + xs.length), weights i :=
  RotationBST.Combo.Rounds.charge_le_interval worker budget restore s offset xs selected weights nonneg

end RotationBST.Combo.Rounds.Results

/-- info: abstract audit passed for `RotationBST.Combo.Rounds.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Rounds.Results allowing [
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract]
