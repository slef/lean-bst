module

public import RotationBST.Algorithms.Combination.Controller.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Worker

/-- A complete request stops at the first completion bit, using exactly its
work as fuel. This is the worker's execution, without controller resets. -/
def Access {σ : Type} (worker : Controller.Worker σ) (side : Bool) (s : σ) (x : Nat) (t : σ) (work : Nat) : Prop :=
  Controller.AttemptRun worker side x work s ⟨t, 0, true⟩ work

inductive Requests {σ : Type} (worker : Controller.Worker σ) (side : Bool) :
    σ → List Nat → σ → Nat → Prop where
  | nil {s : σ} : Requests worker side s [] s 0
  | cons {s t u : σ} {x : Nat} {xs : List Nat} {before after : Nat} :
      Access worker side s x t before → Requests worker side t xs u after →
      Requests worker side s (x :: xs) u (before + after)

/-- An exhausted round completes all but its last request, whose attempt
consumes the remaining budget without completion. The last request is included
even when zero budget remains, matching the round-span coverage convention. -/
inductive ClosedRound {σ : Type} (worker : Controller.Worker σ) (side : Bool) :
    σ → Nat → List Nat → Prop where
  | failed {s : σ} {x fuel work : Nat} {result : Controller.Attempt σ} :
      Controller.AttemptRun worker side x fuel s result work → result.done = false →
      ClosedRound worker side s fuel [x]
  | cons {s : σ} {x fuel work : Nat} {result : Controller.Attempt σ} {xs : List Nat} :
      Controller.AttemptRun worker side x fuel s result work → result.done = true →
      ClosedRound worker side result.state result.left xs →
      ClosedRound worker side s fuel (x :: xs)

end RotationBST.Combo.Worker
