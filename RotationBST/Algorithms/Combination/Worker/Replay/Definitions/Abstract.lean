module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

/-- A visit on a recorded instruction path, including its initial cursor. -/
def Visits (x : Nat) (ops : List Opcode) (cursor : Pointer.Config) : Prop :=
  ∃ before after visited, ops = before ++ after ∧ replay before cursor = some visited ∧ visited.key? = some x

/-- A causal pointer planner. The current state and current request determine
its output; no future request list is supplied. Planning and the retained log
are permitted in the abstract BST model, not claimed as finite-word storage. -/
structure Planner (σ : Type) (saved : Tree) where
  initial : Bool → σ
  tree : Bool → σ → Tree
  plan : Bool → σ → Nat → σ × List Opcode
  initial_tree : ∀ side, tree side (initial side) = saved
  legal : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
    replay (plan side state x).2 ⟨tree side state, []⟩ = some ⟨tree side (plan side state x).1, []⟩
  visits : ∀ side state x, (tree side state).size = saved.size → x < saved.size →
    Visits x (plan side state x).2 ⟨tree side state, []⟩

inductive State (σ : Type) where
  | boundary (state : σ)
  | running (next : σ) (cursor : Pointer.Config) (remaining : List Opcode)

/-- One unit starts planning, each subsequent opcode takes one unit, and one
final unit reports completion. A failed opcode never reports success. -/
def step {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) : State σ → Nat → State σ × Bool
  | .boundary state, x =>
    let planned := planner.plan side state x
    (.running planned.1 ⟨planner.tree side state, []⟩ planned.2, false)
  | .running next _ [], _ => (.boundary next, true)
  | .running next cursor (op :: ops), _ =>
    match perform op cursor with
    | none => (.running next cursor (op :: ops), false)
    | some moved => (.running next moved ops, false)

def worker {σ : Type} {saved : Tree} (planner : Planner σ saved) : Controller.Worker (State σ) :=
  ⟨fun side => .boundary (planner.initial side), step planner⟩

def cursor {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) : State σ → Pointer.Config
  | .boundary state => ⟨planner.tree side state, []⟩
  | .running _ current _ => current

def Ready {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) : State σ → Prop
  | .boundary state => (planner.tree side state).size = saved.size
  | .running next current ops =>
      (planner.tree side next).size = saved.size ∧ replay ops current = some ⟨planner.tree side next, []⟩

def instruction {σ : Type} : State σ → Option Opcode
  | .running _ _ (op :: _) => some op
  | _ => none

/-- Whole requests use the same planner, allowing exact cost/state comparison
with the interruptible worker. Empty input does not invoke planning. -/
def run {σ : Type} {saved : Tree} (planner : Planner σ saved) (side : Bool) : σ → List Nat → σ × Nat
  | state, [] => (state, 0)
  | state, x :: xs =>
    let planned := planner.plan side state x
    let rest := run planner side planned.1 xs
    (rest.1, planned.2.length + 2 + rest.2)

/-- Direct execution of a source policy's request rule, before trace expansion. -/
def policyRun {σ : Type} (next : Bool → σ → Nat → σ × Nat) (side : Bool) : σ → List Nat → σ × Nat
  | state, [] => (state, 0)
  | state, x :: xs =>
    let first := next side state x
    let rest := policyRun next side first.1 xs
    (rest.1, first.2 + rest.2)

end RotationBST.Combo.Worker.Replay
