module

public import RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.CellIO

/-- The snapshot's desired node fields. Indexing is a layout specification;
the operational implementation accepts and returns scalar values at its cursor. -/
def payload (saved : Tree) (key : Nat) : Nat :=
  ((encodedCells saved)[key]?).getD 0

/-- The finite node universe contains this snapshot, regardless of its current
shape. Values outside the saved tree's key universe are not constrained. -/
def Stored (saved : Tree) (data : Nat → Nat) : Prop :=
  ∀ key, key < saved.size → data key = payload saved key

/-- Consume cells in descending key order, undoing each four-opcode packet
locally. This is the emitted instruction stream, not an extra stored log. -/
def inverseCells (codes : List Nat) : List Multifinger.Opcode :=
  codes.flatMap fun code => Multifinger.undo (decodeCell code)

end RotationBST.TreeBuffer.Snapshot.CellIO
