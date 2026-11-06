module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Worker.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Worker.Results
open Controller

theorem completed_unique {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work otherFuel otherWork : Nat}
    {s : σ} {result other : Attempt σ} (first : AttemptRun worker side x fuel s result work)
    (finished : result.done = true) (second : AttemptRun worker side x otherFuel s other otherWork)
    (alsoFinished : other.done = true) : result.state = other.state ∧ work = otherWork :=
  RotationBST.Combo.Controller.AttemptRun.completed_unique first finished second alsoFinished

theorem failed_lt_complete {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work otherFuel otherWork : Nat}
    {s : σ} {result other : Attempt σ} (first : AttemptRun worker side x fuel s result work)
    (failed : result.done = false) (second : AttemptRun worker side x otherFuel s other otherWork)
    (finished : other.done = true) : fuel < otherWork :=
  RotationBST.Combo.Controller.AttemptRun.failed_lt_complete first failed second finished

theorem to_access {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work)
    (finished : result.done = true) : Worker.Access worker side s x result.state work :=
  RotationBST.Combo.Controller.AttemptRun.to_access run finished

theorem Requests.append {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t u : σ} {before after : Nat} {earlier later : List Nat}
    (first : Requests worker side s earlier t before) (second : Requests worker side t later u after) :
    Requests worker side s (earlier ++ later) u (before + after) :=
  RotationBST.Combo.Worker.Requests.append first second

theorem Requests.unique {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t u : σ} {cost otherCost : Nat} {xs : List Nat}
    (first : Requests worker side s xs t cost) (second : Requests worker side s xs u otherCost) :
    t = u ∧ cost = otherCost :=
  RotationBST.Combo.Worker.Requests.unique first second

theorem Requests.length_le_cost {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {cost : Nat} {xs : List Nat} (run : Requests worker side s xs t cost) : xs.length ≤ cost :=
  RotationBST.Combo.Worker.Requests.length_le_cost run

theorem ClosedRound.lower_bound {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {budget cost : Nat} {xs : List Nat}
    (round : ClosedRound worker side s budget xs) (complete : Requests worker side s xs t cost) :
    budget < cost :=
  RotationBST.Combo.Worker.ClosedRound.lower_bound round complete

theorem ClosedRound.prepend {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {before remaining : Nat} {earlier suffix : List Nat}
    (complete : Requests worker side s earlier t before) (round : ClosedRound worker side t remaining suffix) :
    ClosedRound worker side s (before + remaining) (earlier ++ suffix) :=
  RotationBST.Combo.Worker.ClosedRound.prepend complete round

theorem first_closed {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (boundary : Nat) (later : List Nat)
    (cut : Rounds.cuts worker budget restore s offset xs = boundary :: later) :
    ClosedRound worker s.side s.workerState s.left (xs.take (boundary - offset + 1)) :=
  RotationBST.Combo.Worker.first_closed worker budget restore s offset xs boundary later cut

theorem first_lower_bound {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (boundary : Nat) (later : List Nat)
    (cut : Rounds.cuts worker budget restore s offset xs = boundary :: later) (final : σ) (cost : Nat)
    (complete : Requests worker s.side s.workerState (xs.take (boundary - offset + 1)) final cost) :
    s.left < cost :=
  RotationBST.Combo.Worker.first_lower_bound worker budget restore s offset xs boundary later cut final cost complete

end RotationBST.Combo.Worker.Results

/-- info: abstract audit passed for `RotationBST.Combo.Worker.Results`: 10 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Worker.Results allowing [
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract]
