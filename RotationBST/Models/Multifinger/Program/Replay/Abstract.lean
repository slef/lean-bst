module

import RotationBST.Audit.Check
public import RotationBST.Models.Multifinger.Program.Replay.AbstractBridge

@[expose] public section
namespace RotationBST.Multifinger.Replay.Results

/-- Replaying a successful log gives exactly its length in physical operations. -/
theorem physical {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    Pointer.Trace a b ops.length := replay_trace run

theorem record {a b : Pointer.Config} {k : Nat} (trace : Pointer.Trace a b k) :
    ∃ ops, ops.length = k ∧ replay ops a = some b := trace_replay trace

/-- The inverse restores the entire cursor, not just its tree. -/
theorem restore {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    replay (undo ops) b = some a := undo_replay run

theorem inverse_size (ops : List Opcode) : (undo ops).length ≤ 3 * ops.length := undo_length ops

theorem roundtrip {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    replay (ops ++ undo ops) a = some a := replay_roundtrip run

end RotationBST.Multifinger.Replay.Results

/-- info: abstract audit passed for `RotationBST.Multifinger.Replay.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Multifinger.Replay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract]
