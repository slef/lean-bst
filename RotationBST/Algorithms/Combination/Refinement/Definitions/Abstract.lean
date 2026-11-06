module

public import RotationBST.Algorithms.Combination.Controller.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Refinement

/-- A causal pointer interpretation of an abstract worker. Each charged step
emits one legal pointer opcode or keeps the cursor fixed for local bookkeeping.
The invariant also identifies the fixed key set and the common restart tree.
This contract does not assert request service or finite-word storage. -/
structure WorkerModel {σ : Type} (worker : Controller.Worker σ) (saved : Tree) where
  cursor : Bool → σ → Pointer.Config
  Ready : Bool → σ → Prop
  instruction : Bool → σ → Nat → Option Multifinger.Opcode
  restart_ready : ∀ side, Ready side (worker.restart side)
  restart_cursor : ∀ side, cursor side (worker.restart side) = ⟨saved, []⟩
  size : ∀ side state, Ready side state → (cursor side state).tree.size = saved.size
  step_ready : ∀ side state x, Ready side state → x < saved.size → Ready side (worker.step side state x).1
  step_cursor : ∀ side state x, Ready side state → x < saved.size →
    match instruction side state x with
    | none => cursor side (worker.step side state x).1 = cursor side state
    | some op => Multifinger.perform op (cursor side state) = some (cursor side (worker.step side state x).1)

/-- The worker uses finger zero; finger one retains the snapshot scan position.
Both fingers denote nodes of the same tree, including during interruptions. -/
def Represents {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
    (model : WorkerModel worker saved) (data : Nat → Nat) (actual : TreeBuffer.Shared.State Nat 2)
    (side : Bool) (state : σ) : Prop :=
  model.Ready side state ∧ actual.Valid data ∧ actual.tree.erase = (model.cursor side state).tree ∧
    (model.cursor side state).key? = some (actual.position 0)

end RotationBST.Combo.Refinement
