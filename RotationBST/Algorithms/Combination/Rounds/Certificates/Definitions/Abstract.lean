module

public import RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates

/-- A ghost record of one exhausted round: its global request interval and
its actual request values. No record list is stored by the controller. -/
structure Record where
  span : Span
  requests : List Nat
  deriving DecidableEq

/-- The current round began at the fixed restart state, completed `earlier`,
and has exactly the unspent part of its original budget remaining. -/
def Active {σ : Type} (worker : Controller.Worker σ) (budget : Nat) (s : Controller.State σ)
    (earlier : List Nat) : Prop :=
  ∃ spent, Worker.Requests worker s.side (worker.restart s.side) earlier s.workerState spent ∧
    spent + s.left = budget

/-- Extract completed-round proof records while following the actual
controller. The successful retry belongs to the next round's completed prefix. -/
def records {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat) :
    Controller.State σ → Nat → Nat → List Nat → List Nat → List Record
  | _, _, _, _, [] => []
  | s, start, offset, earlier, x :: xs =>
      let next := Controller.serve worker budget restore s x
      if next.done then
        if next.switched then
          ⟨⟨s.side, start, offset + 1⟩, earlier ++ [x]⟩ ::
            records worker budget restore next.state offset (offset + 1) [x] xs
        else records worker budget restore next.state start (offset + 1) (earlier ++ [x]) xs
      else []

end RotationBST.Combo.Rounds.Certificates
