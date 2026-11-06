module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Controller.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Controller.Results

theorem attempt_run {σ : Type} (worker : Worker σ) (side : Bool) (x fuel : Nat) (s : σ) :
    AttemptRun worker side x fuel s (attempt worker side x fuel s)
      (fuel - (attempt worker side x fuel s).left) :=
  RotationBST.Combo.Controller.attempt_run worker side x fuel s

theorem AttemptRun.failed {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work)
    (failed : result.done = false) : result.left = 0 ∧ work = fuel :=
  RotationBST.Combo.Controller.AttemptRun.failed run failed

theorem attempt_extra {σ : Type} (worker : Worker σ) (side : Bool) (x fuel extra : Nat) (s : σ)
    (done : (attempt worker side x fuel s).done = true) :
    attempt worker side x (fuel + extra) s =
      { attempt worker side x fuel s with left := (attempt worker side x fuel s).left + extra } :=
  RotationBST.Combo.Controller.attempt_extra worker side x fuel extra s done

theorem serve_service {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    Service worker budget restore s x (serve worker budget restore s x) :=
  RotationBST.Combo.Controller.serve_service worker budget restore s x

theorem serve_done {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget) (s : State σ) (x : Nat) (valid : x < n) :
    (serve worker budget restore s x).done = true :=
  RotationBST.Combo.Controller.serve_done worker n bound budget restore bounded enough s x valid

theorem serve_left {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat)
    (limit : s.left ≤ budget) : (serve worker budget restore s x).state.left ≤ budget :=
  RotationBST.Combo.Controller.serve_left worker budget restore s x limit

theorem serve_alternates {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    (serve worker budget restore s x).state.side =
      if (serve worker budget restore s x).switched then !s.side else s.side :=
  RotationBST.Combo.Controller.serve_alternates worker budget restore s x

theorem fresh_completes {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget) (side : Bool) (x : Nat) (valid : x < n) :
    (serve worker budget restore ⟨side, worker.restart side, budget⟩ x).switched = false ∧
      (serve worker budget restore ⟨side, worker.restart side, budget⟩ x).work ≤ bound :=
  RotationBST.Combo.Controller.fresh_completes worker n bound budget restore bounded enough side x valid

theorem complete {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget)
    (s : State σ) (limit : s.left ≤ budget) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ final cost switches, Execution worker budget restore s xs final cost switches ∧
      run worker budget restore s xs = some (final, cost) ∧ final.left ≤ budget ∧
      cost ≤ (2 * budget + restore) * xs.length :=
  RotationBST.Combo.Controller.complete worker n bound budget restore bounded enough s limit xs valid

theorem Execution.account {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) :
    cost + t.left = s.left + switches * (budget + restore) :=
  RotationBST.Combo.Controller.Execution.account execution

theorem Execution.switches {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) : switches ≤ xs.length :=
  RotationBST.Combo.Controller.Execution.switches execution

theorem run_append {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (xs ys : List Nat) :
    run worker budget restore s (xs ++ ys) =
      (run worker budget restore s xs).bind fun first =>
        (run worker budget restore first.1 ys).map fun last => (last.1, first.2 + last.2) :=
  RotationBST.Combo.Controller.run_append worker budget restore s xs ys

theorem Execution.left_le {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) (limit : s.left ≤ budget) : t.left ≤ budget :=
  RotationBST.Combo.Controller.Execution.left_le execution limit

theorem Execution.split {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs ys : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s (xs ++ ys) t cost switches) :
    ∃ middle beforeCost afterCost beforeSwitches afterSwitches,
      Execution worker budget restore s xs middle beforeCost beforeSwitches ∧
      Execution worker budget restore middle ys t afterCost afterSwitches ∧
      cost = beforeCost + afterCost ∧ switches = beforeSwitches + afterSwitches :=
  RotationBST.Combo.Controller.Execution.split execution

theorem Execution.window {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches lo hi : Nat}
    (execution : Execution worker budget restore s xs t cost switches) (ordered : lo ≤ hi) :
    ∃ beforeState afterState beforeCost windowCost afterCost beforeSwitches windowSwitches afterSwitches,
      Execution worker budget restore s (xs.take lo) beforeState beforeCost beforeSwitches ∧
      Execution worker budget restore beforeState ((xs.drop lo).take (hi - lo)) afterState windowCost windowSwitches ∧
      Execution worker budget restore afterState (xs.drop hi) t afterCost afterSwitches ∧
      cost = beforeCost + windowCost + afterCost ∧ switches = beforeSwitches + windowSwitches + afterSwitches :=
  RotationBST.Combo.Controller.Execution.window execution ordered

end RotationBST.Combo.Controller.Results

/-- info: abstract audit passed for `RotationBST.Combo.Controller.Results`: 15 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Controller.Results allowing [
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract]
