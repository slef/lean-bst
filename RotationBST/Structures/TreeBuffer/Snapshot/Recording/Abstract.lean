module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording.Results
open Multifinger

/-- Record a fitting local-controller stream one bounded packet at a time. -/
theorem produce (s : State) (valid : s.Valid) (final : Controller.State) (ops : List Opcode)
    (normal : Controller.Run s.control ops final) (halt : Controller.tick final = none)
    (capacity : ops.length ≤ 4 * s.scan.requests.length) :
    ∃ t w r, Run s t ops w r ∧ t.control = final :=
  Recording.produce s valid final ops normal halt capacity

/-- The controller emits exactly the recorded opcode stream. -/
theorem controller {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Controller.Run s.control ops t.control :=
  run.controller

/-- The buffer projection includes every normalization rotation and charged write. -/
theorem buffer {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Scan.Trace s.scan t.scan w r :=
  run.scan

/-- Completed recording halts the controller and fills every pending cell. -/
theorem finished {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r) :
    Controller.tick t.control = none ∧ t.scan.requests = [] :=
  run.finished

/-- Recording combines linear scan accounting with the emitted opcode count. -/
theorem cost {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r)
    (valid : s.Valid) : w + ops.length ≤ 4 * s.scan.tree.size + 4 * ops.length :=
  run.cost valid

/-- Writes store the canonical packed stream in initial scan order. -/
theorem cells {s t : State} {ops : List Opcode} {w r : Nat} (run : Run s t ops w r)
    (valid : s.Valid) :
    Cells.Trace ⟨s.scan, s.data⟩ ⟨t.scan, t.data⟩
      (List.zipWith Cells.Event.write s.scan.requests ((pack s.scan.requests.length ops).map encodeCell)) w r :=
  run.cells valid

/-- A completed normalizer recording stores the exact snapshot payloads. -/
theorem stored (tree : Tree) (data : Nat → Nat) {t : State} {work rotations : Nat}
    (run : Run (initial tree data) t (record tree) work rotations) (nonempty : tree ≠ .nil) :
    CellIO.Stored tree t.data :=
  Run.stored tree data run nonempty

/-- Online packet production and writes cost at most 20n. -/
theorem snapshot (tree : Tree) (data : Nat → Nat) :
    ∃ t work rotations, Run (initial tree data) t (record tree) work rotations ∧
      t.control = ⟨⟨vine tree.size, []⟩, 0, .ascend⟩ ∧ CellIO.Stored tree t.data ∧
      work + (record tree).length ≤ 20 * tree.size :=
  record_snapshot tree data

/-- Recording followed by streaming restoration is a shape-preserving save costing at most 72n. -/
theorem save (tree : Tree) (data : Nat → Nat) :
    ∃ finalData cost, Save data tree finalData cost ∧ CellIO.Stored tree finalData ∧ cost ≤ 72 * tree.size :=
  Recording.save tree data

end RotationBST.TreeBuffer.Snapshot.Recording.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Snapshot.Recording.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Snapshot.Recording.Results allowing [
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
  RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Snapshot.Recording.Definitions.Abstract]
