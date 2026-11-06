module

public import RotationBST.Algorithms.Combination.Online.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Startup.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Online
open TreeBuffer

/-- A fixed, charged preparation, chosen before any request is supplied.
The snapshot and maintained hand are coupled to the same actual shared state. -/
structure Prepared {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : Refinement.WorkerModel worker saved) (budget restore : Nat)
    (fields : Nat → IntervalMetadata.Bounds) (oldData : Nat → Nat) where
  data : Nat → Nat
  contract : Contract model data budget restore
  state : State model data budget
  controller_initial : state.controller = Controller.initial worker budget
  saveEvents : List (Cells.Event Nat)
  saveCost : Nat
  setup : Snapshot.Startup.Execution saved saved.size fields oldData state.actual saveEvents saveCost
  saveBound : saveCost ≤ 1088 * saved.size
  cost : Nat
  trace : Pointer.Trace ⟨saved, []⟩ ⟨state.hand.tree, []⟩ cost
  charged : cost + state.hand.potential ≤ 524 * saveCost

/-- `none` is the original tree before the first request triggers preparation. -/
def Prepared.current {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Prepared model budget restore fields oldData) (s : Option (State model p.data budget)) : Tree :=
  match s with
  | none => saved
  | some ready => ready.hand.tree

/-- The same optional state projected to its logical controller boundary. -/
def Prepared.controller {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    {model : Refinement.WorkerModel worker saved} {budget restore : Nat}
    {fields : Nat → IntervalMetadata.Bounds} {oldData : Nat → Nat}
    (p : Prepared model budget restore fields oldData) (s : Option (State model p.data budget)) : Controller.State σ :=
  match s with
  | none => Controller.initial worker budget
  | some ready => ready.controller

end RotationBST.Combo.Online
