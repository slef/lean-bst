module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording
open Multifinger

/-- The normalizer and buffer finger share the tree. A packet is retained
only within the bounded packet-producing operation below. -/
structure State where
  control : Controller.State
  scan : Scan.State
  data : Nat → Nat

def State.Valid (s : State) : Prop := s.control.cursor.tree = s.scan.tree ∧ s.scan.Valid

/-- A recording execution alternates local normalization of at most four
opcodes with one charged cell write. Packet production stops at capacity or
controller halt. After halt, empty packets pad the remaining node fields.
All lists in this relation are execution witnesses, not accumulated storage. -/
inductive Run : State → State → List Opcode → Nat → Nat → Prop where
  | done {s : State} {control : Controller.State} :
      Controller.Run s.control [] control → Controller.tick control = none → s.scan.requests = [] →
      Run s ⟨control, s.scan, s.data⟩ [] 0 0
  | packet {s u : State} {control : Controller.State} {chunk tail : List Opcode}
      {rotations work later more : Nat} {scan : Scan.State} {data : Nat → Nat} {key : Nat} :
      Controller.Run s.control chunk control → chunk.length ≤ 4 →
      (chunk.length = 4 ∨ Controller.tick control = none) →
      Scan.Trace s.scan { s.scan with tree := control.cursor.tree } 0 rotations → rotations ≤ chunk.length →
      Cells.Trace ⟨{ s.scan with tree := control.cursor.tree }, s.data⟩ ⟨scan, data⟩
        [.write key (encodeCell chunk)] work 0 →
      Run ⟨control, scan, data⟩ u tail later more →
      Run s u (chunk ++ tail) (work + later) (rotations + more)

def initial (tree : Tree) (data : Nat → Nat) : State :=
  ⟨⟨⟨tree, []⟩, 0, .scan⟩, ⟨tree, Streaming.rootPosition tree, 0, false⟩, data⟩

/-- Record the current tree into its node fields, then restore its shape by
streaming those fields backwards. Switching phases resets scalar scan control;
both cursor locations are preserved. -/
def Save (data : Nat → Nat) (tree : Tree) (finalData : Nat → Nat) (cost : Nat) : Prop :=
  ∃ recorded ops work rotations restored reads instructions replayRotations,
    Run (initial tree data) recorded ops work rotations ∧
    recorded.control.cursor = ⟨recorded.scan.tree, []⟩ ∧
    Streaming.Trace recorded.data (Streaming.initial recorded.scan.tree recorded.scan.position)
      restored reads instructions replayRotations ∧
    restored.Done ∧ restored.cursor = ⟨tree, []⟩ ∧ finalData = recorded.data ∧
    cost = ops.length + work + reads + instructions

end RotationBST.TreeBuffer.Snapshot.Recording
