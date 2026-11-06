module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Streaming.Results
open Multifinger

/-- Every unfinished state with a legal remaining stream has a next primitive. -/
theorem progress (data : Nat → Nat) (s : State) (valid : s.Valid)
    (target : Pointer.Config) (executable : replay (remaining data s) s.cursor = some target)
    (unfinished : ¬ s.Done) : ∃ t w p r, Step data s t w p r :=
  next_exists data s valid target executable unfinished

/-- The joint machine finishes within its initial potential. -/
theorem finish (data : Nat → Nat) (s : State) (valid : s.Valid)
    (target : Pointer.Config) (executable : replay (remaining data s) s.cursor = some target) :
    ∃ t w p r, Trace data s t w p r ∧ t.Done ∧ w + p ≤ potential data s :=
  Streaming.finish data s valid target executable

/-- Buffer work and replay work share one decreasing potential. -/
theorem cost {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (valid : s.Valid) :
    w + p + potential data t ≤ potential data s :=
  trace.amortized valid

/-- Replay projection uses exactly the charged pointer-instruction count. -/
theorem physical {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) : Pointer.Trace s.cursor t.cursor p :=
  trace.physical

/-- Buffer projection includes the rotations performed during replay. -/
theorem buffer {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) : Scan.Trace s.scan t.scan w r :=
  trace.scan

/-- Completion executes exactly the originally specified stream. -/
theorem completed {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (done : t.Done) :
    replay (remaining data s) s.cursor = some t.cursor ∧ p = (remaining data s).length :=
  Streaming.completed trace done

/-- Every prefix retains at most twelve opcodes and bounded scan counters. -/
theorem space {data : Nat → Nat} {s t : State} {w p r : Nat}
    (trace : Trace data s t w p r) (valid : s.Valid) :
    t.packet.length ≤ 12 ∧ t.scan.next ≤ s.scan.tree.size ∧ t.scan.position < s.scan.tree.size :=
  trace.space valid

/-- Streaming restoration from the common vine costs at most 52n. -/
theorem restore (saved : Tree) (data : Nat → Nat) (stored : CellIO.Stored saved data) :
    ∃ t w p r, Trace data (initial (vine saved.size) 0) t w p r ∧
      t.Done ∧ t.cursor = ⟨saved, []⟩ ∧ p = (undo (record saved)).length ∧ w + p ≤ 52 * saved.size :=
  Streaming.restore saved data stored

/-- Normalization followed by streaming restoration costs at most 56n. -/
theorem load (saved current : Tree) (same : current.size = saved.size)
    (data : Nat → Nat) (stored : CellIO.Stored saved data) :
    ∃ cost, Load data current saved cost ∧ cost ≤ 56 * current.size :=
  Streaming.load saved current same data stored

end RotationBST.TreeBuffer.Snapshot.Streaming.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Snapshot.Streaming.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Snapshot.Streaming.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.CellIO.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Controller.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract]
