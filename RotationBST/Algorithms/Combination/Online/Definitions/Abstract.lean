module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Requests.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Erasure.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Refinement.Definitions.Abstract
public import RotationBST.Structures.FingerHand.Packed.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Online
open TreeBuffer

/-- Fixed proof obligations for a causal request rule. No future input appears
in the contract; the snapshot and restore charge remain fixed throughout. -/
structure Contract {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (data : Nat → Nat) (budget restore : Nat) : Prop where
  correct : Refinement.Visits.Correct model
  stored : Snapshot.CellIO.Stored saved data
  paid : 841 * saved.size ≤ 15 * restore
  fresh : Controller.FreshBound worker saved.size budget

/-- The controller, annotated virtual tree, and maintained physical hand.
The certificates record invariants, not runtime history or future requests.
Finite-word storage of this representation is a separate refinement. -/
structure State {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (data : Nat → Nat) (budget : Nat) where
  controller : Controller.State σ
  actual : Shared.State Nat 2
  hand : FingerHand.Hand
  represented : Refinement.Represents model data actual controller.side controller.workerState
  boundary : Refinement.Visits.Boundary worker saved.size controller.side controller.workerState
  handRep : hand.Represents actual.erase
  left_le : controller.left ≤ budget

/-- One request preserves the exact controller transition, a legal physical
visit, and a potential bound. The shared visit is retained as well, including
the unchanged snapshot payload read by retries. -/
def Transition {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget : Nat}
    (restore : Nat) (s : State model data budget) (x : Nat) (result : State model data budget × Nat) : Prop :=
  result.1.controller = (Controller.serve worker budget restore s.controller x).state ∧
  Pointer.Serves s.hand.tree result.1.hand.tree x result.2 ∧
  result.2 + result.1.hand.potential ≤
    8384 * (Controller.serve worker budget restore s.controller x).work + s.hand.potential ∧
  ∃ events work, Shared.Requests.Visit s.actual result.1.actual x events work ∧
    Snapshot.Streaming.Refinement.Reads data events ∧
    work ≤ 15 * (Controller.serve worker budget restore s.controller x).work

end RotationBST.Combo.Online
