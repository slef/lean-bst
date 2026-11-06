module

public import RotationBST.Models.Multifinger.Program.Definitions.Abstract

@[expose] public section
namespace RotationBST.Multifinger

/-- Replay a recorded stream on one persistent cursor. Illegal instructions
fail explicitly; neither their target tree nor their target key is supplied. -/
def replay : List Opcode → Pointer.Config → Option Pointer.Config
  | [], cursor => some cursor
  | op :: ops, cursor => (perform op cursor).bind (replay ops)

/-- Undo a primitive instruction while restoring both tree and cursor.
Undoing a rotation requires three instructions because its old parent was demoted. -/
def Opcode.inverse : Opcode → List Opcode
  | .downLeft => [.upLeft]
  | .downRight => [.upRight]
  | .upLeft => [.downLeft]
  | .upRight => [.downRight]
  | .rotateLeftChild => [.downRight, .rotateRightChild, .downLeft]
  | .rotateRightChild => [.downLeft, .rotateLeftChild, .downRight]

/-- Undo in reverse chronological order, expanding each primitive inverse. -/
def undo (ops : List Opcode) : List Opcode := ops.reverse.flatMap Opcode.inverse

end RotationBST.Multifinger
