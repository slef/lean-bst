module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section
namespace RotationBST.Combo.Controller

/-- Two causal workers with a common state type. One call performs one charged
unit and reports whether the current request has completed. `restart` is the
worker state after restoring the fixed initial tree. Physical implementation
of these operations is a separate refinement obligation. -/
structure Worker (σ : Type) where
  restart : Bool → σ
  step : Bool → σ → Nat → σ × Bool

structure Attempt (σ : Type) where
  state : σ
  left : Nat
  done : Bool
  deriving DecidableEq

/-- Run only the current request, stopping immediately on completion or budget
exhaustion. A failed attempt retains its partial worker state for restoration. -/
def attempt {σ : Type} (worker : Worker σ) (side : Bool) (x : Nat) : Nat → σ → Attempt σ
  | 0, s => ⟨s, 0, false⟩
  | fuel + 1, s =>
      let next := worker.step side s x
      if next.2 then ⟨next.1, fuel, true⟩ else attempt worker side x fuel next.1

structure State (σ : Type) where
  side : Bool
  workerState : σ
  left : Nat
  deriving DecidableEq

def initial {σ : Type} (worker : Worker σ) (budget : Nat) : State σ :=
  ⟨false, worker.restart false, budget⟩

structure Result (σ : Type) where
  state : State σ
  done : Bool
  switched : Bool
  work : Nat
  deriving DecidableEq

/-- At most one switch per request. Both branches use only the current input
and state. The supplied restore charge remains explicit. A second failed
attempt is reported as failure, never silently accepted as a served request. -/
def serve {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) : Result σ :=
  let first := attempt worker s.side x s.left s.workerState
  if first.done then
    ⟨⟨s.side, first.state, first.left⟩, true, false, s.left - first.left⟩
  else
    let second := attempt worker (!s.side) x budget (worker.restart (!s.side))
    ⟨⟨!s.side, second.state, second.left⟩, second.done, true,
      s.left - first.left + restore + (budget - second.left)⟩

/-- Operational trace of one attempted request. The budget decreases once per
worker step, and a completion bit stops the attempt immediately. -/
inductive AttemptRun {σ : Type} (worker : Worker σ) (side : Bool) (x : Nat) :
    Nat → σ → Attempt σ → Nat → Prop where
  | exhausted {s : σ} : AttemptRun worker side x 0 s ⟨s, 0, false⟩ 0
  | done {fuel : Nat} {s t : σ} : worker.step side s x = (t, true) →
      AttemptRun worker side x (fuel + 1) s ⟨t, fuel, true⟩ 1
  | more {fuel work : Nat} {s t : σ} {result : Attempt σ} :
      worker.step side s x = (t, false) → AttemptRun worker side x fuel t result work →
      AttemptRun worker side x (fuel + 1) s result (1 + work)

/-- Trace of the controller's one or two attempts. Restoring the original state
is an explicit charged boundary between them, not parallel worker execution. -/
inductive Service {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    Result σ → Prop where
  | finish {first : Attempt σ} {work : Nat} :
      AttemptRun worker s.side x s.left s.workerState first work → first.done = true →
      Service worker budget restore s x ⟨⟨s.side, first.state, first.left⟩, true, false, work⟩
  | switch {first second : Attempt σ} {before after : Nat} :
      AttemptRun worker s.side x s.left s.workerState first before → first.done = false →
      AttemptRun worker (!s.side) x budget (worker.restart (!s.side)) second after →
      Service worker budget restore s x
        ⟨⟨!s.side, second.state, second.left⟩, second.done, true, before + restore + after⟩

/-- The paper's single-access hypothesis at a fresh round, restricted to valid
keys. Larger round budgets will inherit this guarantee. -/
def FreshBound {σ : Type} (worker : Worker σ) (n bound : Nat) : Prop :=
  ∀ side x, x < n → (attempt worker side x bound (worker.restart side)).done = true

/-- Execute a finite online input prefix. A reported failure stops the run. -/
def run {σ : Type} (worker : Worker σ) (budget restore : Nat) : State σ → List Nat → Option (State σ × Nat)
  | s, [] => some (s, 0)
  | s, x :: xs =>
      let next := serve worker budget restore s x
      if next.done then
        (run worker budget restore next.state xs).map fun result => (result.1, next.work + result.2)
      else none

/-- Completed request executions. The switch count is proof accounting, not
additional unbounded runtime history retained by the controller. -/
inductive Execution {σ : Type} (worker : Worker σ) (budget restore : Nat) :
    State σ → List Nat → State σ → Nat → Nat → Prop where
  | nil {s : State σ} : Execution worker budget restore s [] s 0 0
  | cons {s t : State σ} {x : Nat} {xs : List Nat} {cost switches : Nat} :
      (serve worker budget restore s x).done = true →
      Execution worker budget restore (serve worker budget restore s x).state xs t cost switches →
      Execution worker budget restore s (x :: xs) t
        ((serve worker budget restore s x).work + cost)
        ((if (serve worker budget restore s x).switched then 1 else 0) + switches)

end RotationBST.Combo.Controller
