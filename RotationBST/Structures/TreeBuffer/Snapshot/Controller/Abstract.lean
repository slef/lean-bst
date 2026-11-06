module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Controller.Results

/-- A local controller emits exactly the normalizing instruction stream. -/
theorem normalizes (t : Tree) :
    Run ⟨⟨t, []⟩, 0, .scan⟩ (record t) ⟨⟨vine t.size, []⟩, 0, .ascend⟩ := normalization t

theorem halts (t : Tree) : tick ⟨⟨vine t.size, []⟩, 0, .ascend⟩ = none := normalized_halts t

/-- Every emitted opcode has the existing physical pointer semantics. -/
theorem replay {s t : State} {ops : List Multifinger.Opcode} (run : Run s ops t) :
    Multifinger.replay ops s.cursor = some t.cursor := run.replay

/-- All prefixes use a counter bounded by the node count, in addition to a
finite mode and cursor. The recorded log is separate from the controller. -/
theorem counter (t : Tree) {s : State} {ops : List Multifinger.Opcode}
    (run : Run ⟨⟨t, []⟩, 0, .scan⟩ ops s) : s.depth ≤ t.size := counter_bound t run

/-- The focused subtree reserves room for the next right-descent increment. -/
theorem counter_focus (t : Tree) {s : State} {ops : List Multifinger.Opcode}
    (run : Run ⟨⟨t, []⟩, 0, .scan⟩ ops s) : s.depth + s.cursor.focus.size ≤ t.size :=
  counter_focus_bound t run

end RotationBST.TreeBuffer.Snapshot.Controller.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Snapshot.Controller.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Snapshot.Controller.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract]
