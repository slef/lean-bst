module

public import RotationBST.Structures.TreeBuffer.Scan.Abstract
public import RotationBST.Structures.TreeBuffer.Cells.Abstract
public import RotationBST.Models.Pointer.Walk.Abstract
public import RotationBST.Bounds.LazyFinger.Dynamic.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.TreeBuffer
open RotationBST.TreeBuffer.Scan

private def leaf : Tree := .node .nil .nil
private def low : Tree := .node .nil leaf
private def middle : Tree := .node low .nil
private def initialTree : Tree := .node middle .nil
private def turnedMiddle : Tree := .node .nil (.node leaf .nil)
private def turnedTree : Tree := .node turnedMiddle .nil

private def s0 : State := ⟨initialTree, 3, 1, false⟩
private def s1 : State := ⟨initialTree, 2, 1, false⟩
private def s2 : State := ⟨initialTree, 0, 1, false⟩
private def s3 : State := ⟨turnedTree, 0, 1, false⟩
private def s4 : State := ⟨turnedTree, 2, 1, false⟩
private def s5 : State := ⟨turnedTree, 1, 1, false⟩

private def c0 : Pointer.Config := ⟨initialTree, []⟩
private def c1 : Pointer.Config := ⟨middle, [.left .nil]⟩
private def c2 : Pointer.Config := ⟨low, [.left .nil, .left .nil]⟩
private def c3 : Pointer.Config := ⟨turnedMiddle, [.left .nil]⟩
private def c4 : Pointer.Config := ⟨.node leaf .nil, [.right .nil, .left .nil]⟩
private def c5 : Pointer.Config := ⟨leaf, [.left .nil, .right .nil, .left .nil]⟩

-- Start toward key 1 from key 3. After two navigation instructions, rotate the
-- subtree under the other finger. The buffer finger stays on key 0, but its
-- distance to the pending key grows from one to two.
private theorem first : Step s0 s1 1 0 :=
  .move (a := c0) (b := c1) rfl .downLeft rfl rfl (by decide) (by decide)
private theorem second : Step s1 s2 1 0 :=
  .move (a := c1) (b := c2) rfl .downLeft rfl rfl (by decide) (by decide)
private theorem interrupt : Step s2 s3 0 1 := .rotate (.inLeft .right)
private theorem third : Step s3 s4 1 0 :=
  .move (a := c3) (b := c4) rfl .downRight rfl rfl (by decide) (by decide)
private theorem fourth : Step s4 s5 1 0 :=
  .move (a := c4) (b := c5) rfl .downLeft rfl rfl (by decide) (by decide)

example : LazyFinger.distance initialTree 0 1 = 1 ∧ LazyFinger.distance turnedTree 0 1 = 2 := by decide

private theorem interrupted : Trace s0 s5.afterVisit 5 1 :=
  .step first (.step second (.step interrupt (.step third (.step fourth
    (.step (.visit (by decide) (by decide)) .refl)))))

-- The same mid-route interruption lifts to real payload reads with identical
-- cost. Exactly key 1 is read; the untouched suffix remains pending.
example (data : Nat → Nat) : TreeBuffer.Cells.Trace ⟨s0, data⟩ ⟨s5.afterVisit, data⟩
    [.read 1 (data 1)] 5 1 := by
  obtain ⟨keys, run, sequence⟩ := TreeBuffer.Cells.lift_read interrupted
    (by unfold State.Valid; decide) data
  have pending_eq : [1] ++ [2, 3] = keys ++ [2, 3] := sequence
  have keys_eq : keys = [1] := (List.append_cancel_right pending_eq).symm
  simpa [keys_eq] using run

example (data target : Nat → Nat) : TreeBuffer.Cells.Trace ⟨s0, data⟩
    ⟨s5.afterVisit, Function.update data 1 (target 1)⟩ [.write 1 (target 1)] 5 1 := by
  obtain ⟨keys, run, sequence⟩ := TreeBuffer.Cells.lift_write interrupted
    (by unfold State.Valid; decide) target data
  have pending_eq : [1] ++ [2, 3] = keys ++ [2, 3] := sequence
  have keys_eq : keys = [1] := (List.append_cancel_right pending_eq).symm
  simpa [keys_eq, TreeBuffer.Cells.writeMany] using run

example : s5.afterVisit.requests = [2, 3] := by decide
example : 5 ≤ 4 * initialTree.size + 3 := Results.cost interrupted (by unfold State.Valid; decide)
example : ∃ u extra, Trace s0 u (5 + extra) 1 ∧ u.requests = [] ∧ 5 + extra ≤ 19 :=
  Results.completion interrupted (by unfold State.Valid; decide)

-- Reverse traversal uses the same interleaving theorem and explicit visit
-- accounting; the pending list is a derived quantity, not stored scan data.
private def descending : State := ⟨initialTree, 3, 4, true⟩
example : descending.requests = [3, 2, 1, 0] := by decide
example : descending.afterVisit.requests = [2, 1, 0] := by decide
example : ∃ t work, Trace descending t work 0 ∧ t.requests = [] ∧ work ≤ potential descending :=
  Results.finish descending (by unfold State.Valid; decide)
example (t : State) (work rotations : Nat) (trace : Trace descending t work rotations)
    (done : t.requests = []) : 4 ≤ work := by
  have visits := Results.visits trace
  rw [done, List.length_nil, Nat.add_zero] at visits
  simpa [descending, State.requests] using visits

-- A singleton visit has cost one in either direction, even though its movement
-- distance is zero. Already-finished scans admit a zero-work trace.
example : Trace ⟨leaf, 0, 0, false⟩ ⟨leaf, 0, 1, false⟩ 1 0 :=
  .step (.visit (by decide) (by decide)) .refl
example : Trace ⟨leaf, 0, 1, true⟩ ⟨leaf, 0, 0, true⟩ 1 0 :=
  .step (.visit (by decide) (by decide)) .refl
example : Trace ⟨leaf, 0, 0, true⟩ ⟨leaf, 0, 0, true⟩ 0 0 := .refl

-- Navigation-only witnesses cannot hide rotations in a fixed-endpoint trace.
example : Pointer.Walk c0 c2 2 := .step .downLeft (.step .downLeft .refl)
example : Pointer.Trace c0 c2 2 := Pointer.Walk.Results.physical (.step .downLeft (.step .downLeft .refl))
example (k : Nat) (walk : Pointer.Walk c0 c2 k) : 2 ≤ k :=
  LazyFinger.Dynamic.Results.shortest walk 3 0 rfl rfl

end RotationBST.Tests.TreeBuffer
