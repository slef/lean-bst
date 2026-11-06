module

public import RotationBST.Algorithms.Combination.Online.Initialization

@[expose] public section
namespace RotationBST.Combo.Online

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget restore : Nat}

theorem advance_exists (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : ∃ result, Transition restore s x result :=
  transition_exists contract s x valid

/-- A fixed rule chosen from the current state and request alone. Classical
choice is permitted in the abstract pointer model; planning is uncharged. -/
noncomputable def advance (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) : State model data budget × Nat :=
  if valid : x < saved.size then Classical.choose (advance_exists contract s x valid) else (s, 0)

noncomputable def run (contract : Contract model data budget restore) (s : State model data budget) :
    List Nat → State model data budget × Nat
  | [] => (s, 0)
  | x :: xs =>
      let next := advance contract s x
      let rest := run contract next.1 xs
      (rest.1, next.2 + rest.2)

theorem preparation_exists {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    (budget restore : Nat) (fresh : Controller.FreshBound worker saved.size budget)
    (paid : 841 * saved.size ≤ 15 * restore) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    Nonempty (Prepared model budget restore fields oldData) :=
  prepared_nonempty model correct budget restore fresh paid nonempty fields oldData

/-- Initialization is fixed before any request list is presented. -/
noncomputable def prepare (model : Refinement.WorkerModel worker saved) (correct : Refinement.Visits.Correct model)
    (budget restore : Nat) (fresh : Controller.FreshBound worker saved.size budget)
    (paid : 841 * saved.size ≤ 15 * restore) (nonempty : saved ≠ .nil)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) :
    Prepared model budget restore fields oldData :=
  Classical.choice (preparation_exists model correct budget restore fresh paid nonempty fields oldData)

/-- Optional state records whether preparation has run. It is charged exactly
once, on the first request, and never inserted into an empty input. -/
noncomputable def access {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Prepared model budget restore fields oldData) (s : Option (State model p.data budget)) (x : Nat) :
    Option (State model p.data budget) × Nat :=
  match s with
  | none => let next := advance p.contract p.state x; (some next.1, p.cost + next.2)
  | some ready => let next := advance p.contract ready x; (some next.1, next.2)

noncomputable def execute {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Prepared model budget restore fields oldData) (s : Option (State model p.data budget)) :
    List Nat → Option (State model p.data budget) × Nat
  | [] => (s, 0)
  | x :: xs =>
      let next := access p s x
      let rest := execute p next.1 xs
      (rest.1, next.2 + rest.2)

end RotationBST.Combo.Online
