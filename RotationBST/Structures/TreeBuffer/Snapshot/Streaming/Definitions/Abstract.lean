module

public import RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming
open Multifinger

/-- Two persistent cursors share the tree: the replay cursor and the buffer
scan cursor. Only one decoded packet is retained between cell reads. -/
structure State where
  cursor : Pointer.Config
  scan : Scan.State
  packet : List Opcode

def State.Valid (s : State) : Prop :=
  s.cursor.tree = s.scan.tree ∧ s.scan.Valid ∧ s.packet.length ≤ 12

/-- Specification of the still-unexecuted stream; it is not stored by the
machine. The retained `packet` alone is bounded working storage. -/
def remaining (data : Nat → Nat) (s : State) : List Opcode :=
  s.packet ++ CellIO.inverseCells (s.scan.requests.map data)

/-- Navigation and reads pause replay. Executing one opcode updates the common
tree and preserves the buffer cursor key. The scan trace certifies the same
zero or one rotation as the replay step, including its effect on routing. -/
inductive Step (data : Nat → Nat) : State → State → Nat → Nat → Nat → Prop where
  | navigate {s : State} {t : Scan.State} : s.packet = [] →
      Cells.Step ⟨s.scan, data⟩ ⟨t, data⟩ none 1 0 →
      Step data s ⟨s.cursor, t, []⟩ 1 0 0
  | read {s : State} {t : Scan.State} {x value : Nat} : s.packet = [] →
      Cells.Step ⟨s.scan, data⟩ ⟨t, data⟩ (some (.read x value)) 1 0 →
      Step data s ⟨s.cursor, t, undo (decodeCell value)⟩ 1 0 0
  | execute {s : State} {op : Opcode} {ops : List Opcode} {cursor : Pointer.Config} {rotations : Nat} :
      s.packet = op :: ops → perform op s.cursor = some cursor →
      Scan.Trace s.scan { s.scan with tree := cursor.tree } 0 rotations → rotations ≤ 1 →
      Step data s ⟨cursor, { s.scan with tree := cursor.tree }, ops⟩ 0 1 rotations

inductive Trace (data : Nat → Nat) : State → State → Nat → Nat → Nat → Prop where
  | refl {s : State} : Trace data s s 0 0 0
  | step {s t u : State} {w p r v q h : Nat} : Step data s t w p r → Trace data t u v q h →
      Trace data s u (w + v) (p + q) (r + h)

/-- Each replay instruction can increase scan potential by at most three;
four units per unexecuted instruction therefore fund all interruptions. -/
def potential (data : Nat → Nat) (s : State) : Nat :=
  4 * (remaining data s).length + Scan.potential s.scan

def State.Done (s : State) : Prop := s.packet = [] ∧ s.scan.requests = []

/-- Begin descending-cell replay with an empty packet and the replay cursor
at the root. Buffer cursor initialization is an explicit input position. -/
def initial (tree : Tree) (position : Nat) : State :=
  ⟨⟨tree, []⟩, ⟨tree, position, tree.size, true⟩, []⟩

/-- The key of the buffer finger initialized at the current root. Zero only
totalizes the empty tree, where no cell access is performed. -/
def rootPosition (tree : Tree) : Nat := (Pointer.Config.key? ⟨tree, []⟩).getD 0

/-- A load first runs the local normalizer while the buffer finger stays on
its original key, then starts descending-cell replay. The target shape occurs
only as the final result, never as an input to the operational choices.
The normalization log and scan trace are proof witnesses, not stored data. -/
def Load (data : Nat → Nat) (current final : Tree) (cost : Nat) : Prop :=
  ∃ ops normalRotations t w p r,
    Controller.Run ⟨⟨current, []⟩, 0, .scan⟩ ops ⟨⟨vine current.size, []⟩, 0, .ascend⟩ ∧
    Scan.Trace ⟨current, rootPosition current, current.size, true⟩
      ⟨vine current.size, rootPosition current, current.size, true⟩ 0 normalRotations ∧
    normalRotations ≤ ops.length ∧
    Trace data (initial (vine current.size) (rootPosition current)) t w p r ∧
    t.Done ∧ t.cursor = ⟨final, []⟩ ∧ cost = ops.length + w + p

end RotationBST.TreeBuffer.Snapshot.Streaming
