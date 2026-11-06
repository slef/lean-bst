module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Results
open Multifinger

/-- A linear-length normalization log with exact cursor/context preservation. -/
theorem normalization (t : Tree) (cs : List Pointer.Frame) :
    replay (record t) ⟨t, cs⟩ = some ⟨vine t.size, cs⟩ ∧ (record t).length ≤ 4 * t.size :=
  ⟨record_replay t cs, record_length t⟩

/-- The log and universe size determine the entire saved tree. -/
theorem identifies (s t : Tree) (same : s.size = t.size) (logs : record s = record t) : s = t :=
  record_injective s t same logs

/-- Save without changing the tree. This bound counts pointer instructions,
with the cost of writing the retained log to node cells accounted separately. -/
theorem save (t : Tree) :
    Pointer.Trace ⟨t, []⟩ ⟨t, []⟩ (saveProgram t).length ∧ (saveProgram t).length ≤ 16 * t.size :=
  ⟨save_trace t, save_length t⟩

/-- Restore using only the current tree and a saved instruction stream. -/
theorem load (current saved : Tree) (same : current.size = saved.size) :
    Pointer.Trace ⟨current, []⟩ ⟨saved, []⟩ (loadProgram current (record saved)).length ∧
      (loadProgram current (record saved)).length ≤ 16 * current.size :=
  ⟨load_trace current saved same, load_length current saved same⟩

/-- One twelve-bit payload per node suffices, including unused zero packets. -/
theorem storage (t : Tree) : (encodedCells t).length = t.size ∧
    (∀ code ∈ encodedCells t, code < 2 ^ 12) ∧ decodeCells (encodedCells t) = record t :=
  ⟨encodedCells_length t, encodedCells_bound t, decodeCells_encoded t⟩

/-- The packed payloads restore the exact tree in any unchanged ancestor context.
The target appears only in the specification, not as an input to `loadEncoded`. -/
theorem encoded_restore (current saved : Tree) (same : current.size = saved.size) (cs : List Pointer.Frame) :
    replay (loadEncoded current (encodedCells saved)) ⟨current, cs⟩ = some ⟨saved, cs⟩ ∧
      (loadEncoded current (encodedCells saved)).length ≤ 16 * current.size :=
  ⟨loadEncoded_replay current saved same cs, loadEncoded_length current saved same⟩

end RotationBST.TreeBuffer.Snapshot.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Snapshot.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Snapshot.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract]
