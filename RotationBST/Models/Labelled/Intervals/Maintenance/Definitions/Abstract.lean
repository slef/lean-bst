module

public import RotationBST.Models.Labelled.Cursor.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Definitions.Abstract

@[expose] public section
namespace RotationBST.IntervalMetadata.Maintenance

inductive Side where
  | left | right
  deriving DecidableEq

def Side.opcode : Side → Multifinger.Opcode
  | .left => .rotateLeftChild
  | .right => .rotateRightChild

/-- Two saved node entries occupy six scalar registers. The cursor addresses
an explicitly labelled tree; the zipper represents parent links, not a stack
allocated by the controller. -/
structure State where
  cursor : LabelledCursor.Config (Nat × Bounds)
  child : Nat × Bounds
  parent : Nat × Bounds
  deriving DecidableEq

inductive Op where
  | pointer (opcode : Multifinger.Opcode)
  | readChild | readParent
  | writeChild (side : Side)
  | writeParent (side : Side)
  deriving DecidableEq

def Op.moves : Op → Nat
  | .pointer _ => 1
  | _ => 0

def Op.cost : Op → Nat
  | .pointer _ => 1
  | .readChild | .readParent => 3
  | .writeChild _ | .writeParent _ => 2

def childBounds (side : Side) (s : State) : Bounds :=
  match side with
  | .left => ⟨s.child.2.low, s.parent.2.high⟩
  | .right => ⟨s.parent.2.low, s.child.2.high⟩

def parentBounds (side : Side) (s : State) : Bounds :=
  match side with
  | .left => ⟨s.child.1 + 1, s.parent.2.high⟩
  | .right => ⟨s.parent.2.low, s.child.1⟩

/-- Store two interval words at the cursor, retaining the key in place. -/
def writeBounds (c : LabelledCursor.Config (Nat × Bounds)) (bounds : Bounds) :
    Option (LabelledCursor.Config (Nat × Bounds)) :=
  match c.focus with
  | .nil => none
  | .node l (key, _) r => some ⟨.node l (key, bounds) r, c.context⟩

/-- Every read and write is guarded by an existing node at the current cursor.
Writes preserve its stored key and replace only the two interval words. -/
def tick (op : Op) (s : State) : Option State := do
  match op with
  | .pointer opcode => return { s with cursor := ← LabelledCursor.perform opcode s.cursor }
  | .readChild => return { s with child := ← s.cursor.read }
  | .readParent => return { s with parent := ← s.cursor.read }
  | .writeChild side => return { s with cursor := ← writeBounds s.cursor (childBounds side s) }
  | .writeParent side => return { s with cursor := ← writeBounds s.cursor (parentBounds side s) }

def run : List Op → State → Option State
  | [], s => some s
  | op :: ops, s => (tick op s).bind (run ops)

def program : Side → List Op
  | .left => [.readChild, .pointer .upLeft, .readParent, .pointer .downLeft,
      .pointer .rotateLeftChild, .writeChild .left, .pointer .downRight,
      .writeParent .left, .pointer .upRight]
  | .right => [.readChild, .pointer .upRight, .readParent, .pointer .downRight,
      .pointer .rotateRightChild, .writeChild .right, .pointer .downLeft,
      .writeParent .right, .pointer .upLeft]

/-- The fixed program uses six word reads, four word writes, four moves,
and one rotation. It begins at the child and finishes at that promoted node. -/
def maintain (side : Side) (s : State) : Option State := run (program side) s

def charge (ops : List Op) : Nat := (ops.map Op.cost).sum

def pointerCount (ops : List Op) : Nat :=
  (ops.filter fun op => match op with | .pointer _ => true | _ => false).length

end RotationBST.IntervalMetadata.Maintenance
