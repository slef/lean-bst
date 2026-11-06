module

public import RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Refinement.Visits

/-- A request boundary reached by completed valid requests of one worker.
This is a proof certificate, not a stored runtime history. -/
def Boundary {σ : Type} (worker : Controller.Worker σ) (n : Nat) (side : Bool) (state : σ) : Prop :=
  ∃ earlier spent, Worker.Requests worker side (worker.restart side) earlier state spent ∧ ∀ x ∈ earlier, x < n

/-- Cursor visits along exactly the consumed worker steps, including the
initial and final cursor. Completion need not occur at the requested key. -/
def Seen {σ : Type} {worker : Controller.Worker σ} {saved : Tree} (model : WorkerModel worker saved)
    (side : Bool) (x : Nat) : Nat → σ → Prop
  | 0, state => (model.cursor side state).key? = some x
  | count + 1, state => (model.cursor side state).key? = some x ∨ Seen model side x count (worker.step side state x).1

/-- The input algorithm's request-correctness contract is imposed only at
reachable request boundaries. It allows cleanup after visiting the key and
does not assume anything about the controller's eventual physical trace. -/
def Correct {σ : Type} {worker : Controller.Worker σ} {saved : Tree} (model : WorkerModel worker saved) : Prop :=
  ∀ side state x final work, Boundary worker saved.size side state → x < saved.size →
    Worker.Access worker side state x final work → Seen model side x work state

end RotationBST.Combo.Refinement.Visits
