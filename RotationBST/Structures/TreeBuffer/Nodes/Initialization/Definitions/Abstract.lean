module

public import RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Initialization.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes.Initialization
open LabelledCursor

/-- Initial finite layout with arbitrary routing words and existing keys/cells.
This is a representation specification, not an initializing traversal. -/
def raw {α : Type} (fields : Nat → IntervalMetadata.Bounds) (data : Nat → α) :
    Tree → Nat → LabelledTree (Entry α)
  | .nil, _ => .nil
  | .node l r, lo =>
      let key := lo + l.size
      .node (raw fields data l lo) ⟨key, fields key, data key⟩ (raw fields data r (key + 1))

structure State (α : Type) where
  cursor : Config (Entry α)
  pending : IntervalMetadata.Bounds
  mode : IntervalMetadata.Initialization.Mode

/-- Stackless initialization on actual combined nodes. Reads use the current
node's stored key and bounds; writes leave its key and snapshot cell intact.
Child dispatch costs four, bounds writes two, null checks and returns one. -/
def tick {α : Type} (s : State α) : Option (Nat × State α) :=
  match s.mode, s.cursor.focus, s.cursor.context with
  | .write, .node l e r, cs =>
      some (2, ⟨⟨.node l { e with bounds := s.pending } r, cs⟩, s.pending, .left⟩)
  | .left, .node .nil _ _, _ => some (1, { s with mode := .right })
  | .left, .node (.node a e b) parent r, cs =>
      some (4, ⟨⟨.node a e b, .left parent r :: cs⟩, ⟨parent.bounds.low, parent.key⟩, .write⟩)
  | .right, .node _ _ .nil, _ => some (1, { s with mode := .up })
  | .right, .node l parent (.node a e b), cs =>
      some (4, ⟨⟨.node a e b, .right l parent :: cs⟩, ⟨parent.key + 1, parent.bounds.high⟩, .write⟩)
  | .up, .node a e b, .left parent r :: cs =>
      some (1, { s with cursor := ⟨.node (.node a e b) parent r, cs⟩, mode := .right })
  | .up, .node a e b, .right l parent :: cs =>
      some (1, { s with cursor := ⟨.node l parent (.node a e b), cs⟩ })
  | _, _, _ => none

inductive Run {α : Type} : State α → State α → Nat → Prop where
  | refl {s : State α} : Run s s 0
  | step {s t u : State α} {cost rest : Nat} : tick s = some (cost, t) → Run t u rest → Run s u (cost + rest)

def initial {α : Type} (tree : LabelledTree (Entry α)) (n : Nat) : State α :=
  ⟨⟨tree, []⟩, ⟨0, n⟩, .write⟩

/-- Bounded tail loop; fuel and the accumulated work are scalar registers. -/
def runLoop {α : Type} : Nat → Nat → State α → Option (Nat × State α)
  | 0, spent, s => match tick s with
    | none => some (spent, s)
    | some _ => none
  | fuel + 1, spent, s => match tick s with
    | none => some (spent, s)
    | some (cost, next) => runLoop fuel (spent + cost) next

def runFuel {α : Type} (fuel : Nat) (s : State α) : Option (Nat × State α) := runLoop fuel 0 s

end RotationBST.TreeBuffer.Nodes.Initialization
