module

public import RotationBST.Models.Labelled.Intervals.Definitions.Abstract
public import RotationBST.Models.Pointer.Walk.Definitions.Abstract

@[expose] public section
namespace RotationBST.IntervalMetadata.Initialization

inductive Mode where
  | write | left | right | up
  deriving DecidableEq

/-- A stackless traversal: one cursor, a finite mode, and two pending bound
registers. Ancestor information remains in parent links and initialized fields. -/
structure State where
  cursor : Pointer.Config
  fields : Nat → Bounds
  pending : Bounds
  mode : Mode

/-- Initialize two bound words, inspect a child link, or follow a parent link.
A descent charges three word reads (key and bounds) and one pointer move;
a write charges two word writes. Null-link/control checks cost one unit.
As in the pointer shape model, offset plus left size denotes the stored cursor
key; its recursive evaluation is not part of this abstract word-cost model. -/
def tick (s : State) : Option (Nat × State) :=
  match s.mode, s.cursor.focus, s.cursor.context with
  | .write, .node l _, _ =>
      some (2, { s with fields := Function.update s.fields (Pointer.offset s.cursor.context + l.size) s.pending, mode := .left })
  | .left, .node .nil _, _ => some (1, { s with mode := .right })
  | .left, .node (.node a b) r, cs =>
      let key := Pointer.offset cs + (Tree.node a b).size
      some (4, ⟨⟨.node a b, .left r :: cs⟩, s.fields, ⟨(s.fields key).low, key⟩, .write⟩)
  | .right, .node _ .nil, _ => some (1, { s with mode := .up })
  | .right, .node l (.node a b), cs =>
      let key := Pointer.offset cs + l.size
      some (4, ⟨⟨.node a b, .right l :: cs⟩, s.fields, ⟨key + 1, (s.fields key).high⟩, .write⟩)
  | .up, .node a b, .left r :: cs =>
      some (1, { s with cursor := ⟨.node (.node a b) r, cs⟩, mode := .right })
  | .up, .node a b, .right l :: cs =>
      some (1, { s with cursor := ⟨.node l (.node a b), cs⟩ })
  | _, _, _ => none

inductive Run : State → State → Nat → Prop where
  | refl {s : State} : Run s s 0
  | step {s t u : State} {cost rest : Nat} : tick s = some (cost, t) → Run t u rest → Run s u (cost + rest)

/-- Mathematical effect of the traversal, used only to state and prove its
output. Runtime child bounds are computed from local keys and stored fields. -/
def populate : Tree → Nat → (Nat → Bounds) → (Nat → Bounds)
  | .nil, _, fields => fields
  | .node l r, lo, fields =>
      populate r (lo + l.size + 1)
        (populate l lo (Function.update fields (lo + l.size) ⟨lo, lo + (Tree.node l r).size⟩))

def work : Tree → Nat
  | .nil => 0
  | .node l r => 2 + (if l = .nil then 1 else 5 + work l) + (if r = .nil then 1 else 5 + work r)

def initial (tree : Tree) (n : Nat) (fields : Nat → Bounds) : State :=
  ⟨⟨tree, []⟩, fields, ⟨0, n⟩, .write⟩

/-- A word-size invariant. The limit may be larger than the key universe to
allow arbitrary old word contents; only two bounds are held in registers. -/
def State.Bounded (limit : Nat) (s : State) : Prop :=
  s.cursor.tree.size ≤ limit ∧ s.pending.low ≤ limit ∧ s.pending.high ≤ limit ∧
    ∀ x, (s.fields x).low ≤ limit ∧ (s.fields x).high ≤ limit

/-- Tail-recursive bounded loop. Fuel and the accumulated charge are scalar
registers; no return stack or instruction list is retained by the controller. -/
def runLoop : Nat → Nat → State → Option (Nat × State)
  | 0, spent, s => match tick s with
    | none => some (spent, s)
    | some _ => none
  | fuel + 1, spent, s => match tick s with
    | none => some (spent, s)
    | some (cost, next) => runLoop fuel (spent + cost) next

/-- Execute the initializer with an explicit loop budget. -/
def runFuel (fuel : Nat) (s : State) : Option (Nat × State) := runLoop fuel 0 s

end RotationBST.IntervalMetadata.Initialization
