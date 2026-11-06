module

public import RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Maintenance.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Access.Definitions.Abstract
public import RotationBST.Models.Labelled.Metadata.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Nodes

/-- One physical node stores its key, routing bounds, and independent buffer cell. -/
structure Entry (α : Type) where
  key : Nat
  bounds : IntervalMetadata.Bounds
  cell : α
  deriving DecidableEq

def Entry.routing {α : Type} (e : Entry α) : Nat × IntervalMetadata.Bounds := (e.key, e.bounds)
def Entry.payload {α : Type} (e : Entry α) : Nat × α := (e.key, e.cell)

/-- Finite representation of the shared routing annotation and saved cells.
This recursive layout is a specification, not a runtime rebuilding operation. -/
def label {α : Type} (data : Nat → α) : Tree → Nat → LabelledTree (Entry α)
  | .nil, _ => .nil
  | .node l r, lo =>
      let key := lo + l.size
      .node (label data l lo) ⟨key, ⟨lo, lo + (Tree.node l r).size⟩, data key⟩
        (label data r (key + 1))

/-- Separate projections are specifications; neither is evaluated as a tree
traversal by the node operations. -/
def Routing {α : Type} (c : LabelledCursor.Config (Entry α)) : Prop :=
  IntervalMetadata.Access.Canonical (c.map Entry.routing)

def Stored {α : Type} (data : Nat → α) (c : LabelledCursor.Config (Entry α)) : Prop :=
  (c.map Entry.payload).tree = Metadata.label data c.erase.tree 0

structure State (α : Type) where
  cursor : LabelledCursor.Config (Entry α)
  child : Nat × IntervalMetadata.Bounds
  parent : Nat × IntervalMetadata.Bounds
  deriving DecidableEq

def State.routing {α : Type} (s : State α) : IntervalMetadata.Maintenance.State :=
  ⟨s.cursor.map Entry.routing, s.child, s.parent⟩

/-- Update only the two bound words; the cell stays in its existing node. -/
def writeBounds {α : Type} (c : LabelledCursor.Config (Entry α)) (bounds : IntervalMetadata.Bounds) :
    Option (LabelledCursor.Config (Entry α)) :=
  match c.focus with
  | .nil => none
  | .node l e r => some ⟨.node l { e with bounds := bounds } r, c.context⟩

/-- The same charged instruction set as interval maintenance, with independent
cell fields carried through each pointer operation and left alone by writes. -/
def tick {α : Type} (op : IntervalMetadata.Maintenance.Op) (s : State α) : Option (State α) := do
  match op with
  | .pointer opcode => return { s with cursor := ← LabelledCursor.perform opcode s.cursor }
  | .readChild => return { s with child := (← s.cursor.read).routing }
  | .readParent => return { s with parent := (← s.cursor.read).routing }
  | .writeChild side => return { s with cursor := ← writeBounds s.cursor (IntervalMetadata.Maintenance.childBounds side s.routing) }
  | .writeParent side => return { s with cursor := ← writeBounds s.cursor (IntervalMetadata.Maintenance.parentBounds side s.routing) }

def run {α : Type} : List IntervalMetadata.Maintenance.Op → State α → Option (State α)
  | [], s => some s
  | op :: ops, s => (tick op s).bind (run ops)

def maintain {α : Type} (side : IntervalMetadata.Maintenance.Side) (s : State α) : Option (State α) :=
  run (IntervalMetadata.Maintenance.program side) s

/-- Navigation reads only key and interval fields, with the same four-unit
charge as the routing-only machine. -/
def route {α : Type} (target : Nat) (c : LabelledCursor.Config (Entry α)) :
    Option (Nat × LabelledCursor.Config (Entry α)) := do
  let e ← c.read
  let direction ← Pointer.Routing.choose ⟨e.bounds.low, e.key, e.bounds.high⟩ target
  let next ← match direction with
    | .left => LabelledCursor.perform .downLeft c
    | .right => LabelledCursor.perform .downRight c
    | .parent => match c.context with
      | .left _ _ :: _ => LabelledCursor.perform .upLeft c
      | .right _ _ :: _ => LabelledCursor.perform .upRight c
      | [] => none
  return (4, next)

/-- A cell read returns one stored word without reading the routing fields. -/
def readCell {α : Type} (c : LabelledCursor.Config (Entry α)) : Option (Nat × α) :=
  c.read.map fun e => (1, e.cell)

/-- A cell write charges one word and preserves the key and routing bounds. -/
def writeCell {α : Type} (c : LabelledCursor.Config (Entry α)) (value : α) :
    Option (Nat × LabelledCursor.Config (Entry α)) :=
  match c.focus with
  | .nil => none
  | .node l e r => some (1, ⟨.node l { e with cell := value } r, c.context⟩)

end RotationBST.TreeBuffer.Nodes
