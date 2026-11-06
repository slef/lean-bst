module

public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot
open Multifinger

/-- Canonical right path on the same inorder keys. -/
def vine : Nat → Tree
  | 0 => .nil
  | n + 1 => .node .nil (vine n)

/-- Each normalization rotation or advance decreases this measure by one. -/
def work : Tree → Nat
  | .nil => 0
  | .node l r => 2 * l.size + 1 + work r

/-- Recorded normalization instructions. The fuel is sufficient when it bounds
`work`; exhausted fuel only totalizes malformed calls to the helper. -/
def recordFuel : Nat → Tree → List Opcode
  | 0, _ => []
  | _ + 1, .nil => []
  | _ + 1, .node .nil .nil => []
  | fuel + 1, .node .nil (.node a b) =>
      .downRight :: (recordFuel fuel (.node a b) ++ [.upRight])
  | fuel + 1, .node (.node a b) c =>
      .downLeft :: .rotateLeftChild :: recordFuel fuel (.node a (.node b c))

/-- A snapshot contains only primitive opcodes, not a copy of the saved tree. -/
def record (t : Tree) : List Opcode := recordFuel (work t) t

/-- Run normalization and immediately undo it, leaving the saved tree in place.
The normalization prefix is the retained snapshot. -/
def saveProgram (t : Tree) : List Opcode := record t ++ undo (record t)

/-- Normalize the current tree, then undo the saved log. The target tree is not
an argument: its structure is recovered solely from the recorded instructions. -/
def loadProgram (current : Tree) (saved : List Opcode) : List Opcode :=
  record current ++ undo saved

/-- Pack at most four opcodes into each of a fixed number of inorder cells.
Unused cells are empty; inputs exceeding capacity are truncated by the helper. -/
def pack : Nat → List Opcode → List (List Opcode)
  | 0, _ => []
  | n + 1, ops => ops.take 4 :: pack n (ops.drop 4)

/-- The saved instruction stream occupies exactly one bounded packet per node. -/
def cells (t : Tree) : List (List Opcode) := pack t.size (record t)

/-- Nonzero base-seven digits reserve zero for the end of a packet. -/
def opcodeDigit : Opcode → Nat
  | .downLeft => 1
  | .downRight => 2
  | .upLeft => 3
  | .upRight => 4
  | .rotateLeftChild => 5
  | .rotateRightChild => 6

def digitOpcode : Nat → Option Opcode
  | 1 => some .downLeft
  | 2 => some .downRight
  | 3 => some .upLeft
  | 4 => some .upRight
  | 5 => some .rotateLeftChild
  | 6 => some .rotateRightChild
  | _ => none

def encodeCell : List Opcode → Nat
  | [] => 0
  | op :: ops => opcodeDigit op + 7 * encodeCell ops

/-- Four decoding rounds suffice for every stored cell. -/
def decodeFuel : Nat → Nat → List Opcode
  | 0, _ => []
  | fuel + 1, code =>
      match digitOpcode (code % 7) with
      | none => []
      | some op => op :: decodeFuel fuel (code / 7)

def decodeCell (code : Nat) : List Opcode := decodeFuel 4 code

def encodedCells (t : Tree) : List Nat := (cells t).map encodeCell

def decodeCells (codes : List Nat) : List Opcode := (codes.map decodeCell).flatten

def loadEncoded (current : Tree) (codes : List Nat) : List Opcode := loadProgram current (decodeCells codes)

end RotationBST.TreeBuffer.Snapshot
