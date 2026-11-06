module

import RotationBST.Audit.Check
public import RotationBST.Structures.TreeBuffer.Scan.AbstractBridge

@[expose] public section
namespace RotationBST.TreeBuffer.Scan.Results

/-- The pending scan is a linear-size potential in either direction. -/
theorem initial (s : State) (valid : s.Valid) : potential s ≤ 4 * s.tree.size := potential_le s valid

/-- Linear traversal accounting from Lemma 9 of arXiv:1304.7604. Rotations can
interrupt the route between two cells. Counts include the scan's node visits.
The operational rule follows a shortest route toward each pending cell. -/
theorem cost {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) : work ≤ 4 * s.tree.size + 3 * rotations := trace.cost valid

/-- Include the cost of the external rotations themselves. -/
theorem total {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) : work + rotations ≤ 4 * s.tree.size + 4 * rotations := trace.total_cost valid

/-- Routing is always possible using a real parent/child pointer primitive. -/
theorem progress (s : State) (valid : s.Valid) (pending : s.requests ≠ []) :
    ∃ t, Step s t 1 0 := next_exists s valid pending

theorem finish (s : State) (valid : s.Valid) :
    ∃ t work, Trace s t work 0 ∧ t.requests = [] ∧ work ≤ potential s := Scan.finish s valid

/-- Every finite interleaved prefix can be completed within the same bound. -/
theorem completion {s t : State} {work rotations : Nat} (trace : Trace s t work rotations)
    (valid : s.Valid) :
    ∃ u extra, Trace s u (work + extra) rotations ∧ u.requests = [] ∧
      work + extra ≤ 4 * s.tree.size + 3 * rotations := complete_after trace valid

/-- Completed scans pay for every pending cell, including repeated-key-free
singleton scans. Navigation and rotations cannot silently skip visits. -/
theorem visits {s t : State} {work rotations : Nat} (trace : Trace s t work rotations) :
    s.requests.length ≤ work + t.requests.length := trace.visits_le

/-- Scan movement can be selected from the interval fields at the cursor. -/
theorem route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : Pointer.Config) (tree : cursor.tree = s.tree) (key : cursor.key? = some s.position)
    (view : Pointer.Routing.View) (fields : view.Valid cursor) (different : s.position ≠ s.target) :
    ∃ next position, Pointer.Routing.next view cursor s.target = some next ∧
      Step s { s with tree := next.tree, position := position } 1 0 :=
  local_route s valid pending cursor tree key view fields different

/-- Read initialized interval fields at the cursor to choose the next scan move. -/
theorem fields_route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : Pointer.Config) (tree : cursor.tree = s.tree) (key : cursor.key? = some s.position)
    (fields : Nat → IntervalMetadata.Bounds)
    (initialized : Metadata.label fields s.tree 0 = IntervalMetadata.label s.tree 0)
    (different : s.position ≠ s.target) :
    ∃ next position,
      Pointer.Routing.next ⟨(fields s.position).low, s.position, (fields s.position).high⟩ cursor s.target = some next ∧
      Step s { s with tree := next.tree, position := position } 1 0 :=
  stored_route s valid pending cursor tree key fields initialized different

/-- Charged routing with explicit stored keys and fields. -/
theorem labelled_route (s : State) (valid : s.Valid) (pending : s.requests ≠ [])
    (cursor : LabelledCursor.Config (Nat × IntervalMetadata.Bounds))
    (canonical : IntervalMetadata.Access.Canonical cursor)
    (tree : cursor.erase.tree = s.tree) (bounds : IntervalMetadata.Bounds)
    (read : cursor.read = some (s.position, bounds)) (different : s.position ≠ s.target) :
    ∃ next position, IntervalMetadata.Access.route s.target cursor = some (4, next) ∧
      Step s { s with tree := next.erase.tree, position := position } 1 0 ∧
      IntervalMetadata.Access.Canonical next :=
  Scan.labelled_route s valid pending cursor canonical tree bounds read different

end RotationBST.TreeBuffer.Scan.Results

/-- info: abstract audit passed for `RotationBST.TreeBuffer.Scan.Results`: 10 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.TreeBuffer.Scan.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Scan.Definitions.Abstract,
  RotationBST.Models.Pointer.Routing.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Access.Definitions.Abstract]
