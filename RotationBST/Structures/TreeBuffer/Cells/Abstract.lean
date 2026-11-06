module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Cells.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Cells.Results

/-- Reads return the payload of the cursor node. -/
theorem read_local {α : Type} {s t : State α} {x : Nat} {value : α} {k r : Nat}
    (step : Step s t (some (.read x value)) k r) :
    x = s.scan.position ∧ value = s.data x ∧ Metadata.At (Metadata.label s.data s.scan.tree 0) x value :=
  read_at step

/-- Writes change only the cursor node payload. -/
theorem write_local {α : Type} {s t : State α} {x : Nat} {value : α} {k r : Nat}
    (step : Step s t (some (.write x value)) k r) :
    x = s.scan.position ∧
      Metadata.Write (Metadata.label s.data s.scan.tree 0) x value (Metadata.label t.data t.scan.tree 0) ∧
      (∀ y, y ≠ x → t.data y = s.data y) :=
  write_at step

/-- The event stream visits exactly a prefix of the pending keys. -/
theorem order {α : Type} {s t : State α} {events : List (Event α)} {k r : Nat}
    (trace : Trace s t events k r) : s.scan.requests = events.map Event.key ++ t.scan.requests :=
  trace.requests

/-- Scan accounting includes every read and write. -/
theorem cost {α : Type} {s t : State α} {events : List (Event α)} {k r : Nat}
    (trace : Trace s t events k r) (valid : s.scan.Valid) : k ≤ 4 * s.scan.tree.size + 3 * r :=
  trace.cost valid

/-- Completed interleaved scans read the full pending stream. -/
theorem read_completed {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (done : t.requests = []) (data : Nat → α) :
    Trace ⟨s, data⟩ ⟨t, data⟩ (s.requests.map fun x => Event.read x (data x)) work rotations :=
  read_complete trace valid done data

/-- Completed interleaved scans set exactly the pending fields. -/
theorem write_completed {α : Type} {s t : Scan.State} {work rotations : Nat}
    (trace : Scan.Trace s t work rotations) (valid : s.Valid) (done : t.requests = []) (target data : Nat → α) :
    ∃ final, Trace ⟨s, data⟩ ⟨t, final⟩ (s.requests.map fun x => Event.write x (target x)) work rotations ∧
      ∀ x, final x = if x ∈ s.requests then target x else data x :=
  write_complete trace valid done target data

/-- Whole-buffer forward read with linear charged work. -/
theorem read_all {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (data : Nat → α) :
    ∃ t work, Trace ⟨⟨tree, position, 0, false⟩, data⟩ ⟨t, data⟩
      ((List.range tree.size).map fun x => Event.read x (data x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size :=
  Cells.read_all tree position present data

/-- Whole-buffer write with linear charged work. -/
theorem write_all {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (target data : Nat → α) :
    ∃ t final work, Trace ⟨⟨tree, position, 0, false⟩, data⟩ ⟨t, final⟩
      ((List.range tree.size).map fun x => Event.write x (target x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size ∧
      ∀ x, final x = if x < tree.size then target x else data x :=
  Cells.write_all tree position present target data

/-- Whole-buffer reverse read with linear charged work. -/
theorem read_reverse {α : Type} (tree : Tree) (position : Nat) (present : position < tree.size)
    (data : Nat → α) :
    ∃ t work, Trace ⟨⟨tree, position, tree.size, true⟩, data⟩ ⟨t, data⟩
      ((List.range tree.size).reverse.map fun x => Event.read x (data x)) work 0 ∧
      t.requests = [] ∧ work ≤ 4 * tree.size :=
  read_all_reverse tree position present data

/-- Advance to and write exactly one pending cell. -/
theorem write_next {α : Type} (s : Scan.State) (valid : s.Valid) (pending : s.requests ≠ [])
    (data : Nat → α) (value : α) :
    ∃ t work, Trace ⟨s, data⟩ ⟨t, Function.update data s.target value⟩
      [.write s.target value] work 0 ∧ s.requests = s.target :: t.requests :=
  Cells.write_next s valid pending data value

/-- The observed write stream determines the final node fields. -/
theorem writes {α : Type} {s t : State α} {target : Nat → α} {keys : List Nat} {w r : Nat}
    (trace : Trace s t (keys.map fun x => Event.write x (target x)) w r) (x : Nat) :
    t.data x = if x ∈ keys then target x else s.data x :=
  trace.writes x

end RotationBST.TreeBuffer.Cells.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Cells.Results`: 11 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Cells.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Cells.Definitions.Abstract]
