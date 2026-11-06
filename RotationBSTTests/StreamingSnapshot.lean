module

public import RotationBST.Structures.TreeBuffer.Snapshot.Streaming.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.StreamingSnapshot
open Multifinger TreeBuffer Snapshot Streaming

private def leaf : Tree := .node .nil .nil
private def saved : Tree := .node (.node leaf .nil) .nil
private def vineThree : Tree := .node .nil (.node .nil leaf)
private def balanced : Tree := .node leaf leaf
private def data : Nat → Nat := CellIO.payload saved

-- Read the last nonempty packet, then execute its first two instructions.
-- The second opcode rotates the tree while the buffer finger remains at key 0.
private def before : State := ⟨⟨vineThree, []⟩, ⟨vineThree, 0, 1, true⟩, []⟩
private def readPacket : State := ⟨before.cursor, before.scan.afterVisit, undo (decodeCell 1800)⟩
private def moved : State :=
  ⟨⟨.node .nil leaf, [.right .nil]⟩, readPacket.scan, readPacket.packet.tail⟩
private def rotated : State :=
  ⟨⟨balanced, []⟩, { moved.scan with tree := balanced }, moved.packet.tail⟩

private theorem readStep : Step data before readPacket 1 0 0 :=
  .read rfl (.read (by decide) (by decide) rfl)
private theorem moveStep : Step data readPacket moved 0 1 0 :=
  .execute (op := .downRight) (by decide) (by decide) .refl (by decide)
private theorem rotateStep : Step data moved rotated 0 1 1 :=
  .execute (op := .rotateRightChild) (by decide) (by decide) (.step (.rotate .left) .refl) (by decide)
private theorem run : Trace data before rotated 1 2 1 :=
  .step readStep (.step moveStep (.step rotateStep .refl))

example : readPacket.packet.length = 8 ∧ rotated.packet.length = 6 := by decide
example : rotated.scan.position = 0 ∧ rotated.scan.tree = balanced := by decide
example : (Metadata.label data balanced 0).erase = balanced := Metadata.label_erase _ _ _
example : Pointer.Trace before.cursor rotated.cursor 2 := Results.physical run
example : Scan.Trace before.scan rotated.scan 1 1 := Results.buffer run
example : rotated.packet.length ≤ 12 ∧ rotated.scan.next ≤ before.scan.tree.size ∧
    rotated.scan.position < before.scan.tree.size := Results.space run (by unfold Streaming.State.Valid Scan.State.Valid; decide)
example : 1 + 2 + potential data rotated ≤ potential data before :=
  Results.cost run (by unfold Streaming.State.Valid Scan.State.Valid; decide)

-- A packet cannot be overwritten by fetching the next cell before execution.
example (t : State) : ¬ Step data readPacket t 1 0 0 := by
  intro step
  cases step with
  | navigate empty _ => have bad := congrArg List.length empty; contradiction
  | read empty _ => have bad := congrArg List.length empty; contradiction

-- Malformed large cell values still decode to bounded working storage.
example : (undo (decodeCell (7 ^ 9 - 1))).length ≤ 12 := packet_bound _

example : ∃ t w p r, Trace data (initial (vine saved.size) 0) t w p r ∧
    t.Done ∧ t.cursor = ⟨saved, []⟩ ∧ p = (undo (record saved)).length ∧ w + p ≤ 52 * saved.size :=
  Results.restore saved data (fun _ _ => rfl)

-- Loading from a different shape starts both fingers at its root; the buffer
-- stays at that key through normalization and is charged for later navigation.
example : rootPosition saved = 2 ∧ rootPosition vineThree = 0 := by decide
example : ∃ cost, Load data balanced saved cost ∧ cost ≤ 56 * balanced.size :=
  Results.load saved balanced (by decide) data (fun _ _ => rfl)
example : ∃ cost, Load (fun _ => 0) .nil .nil cost ∧ cost ≤ 0 :=
  Results.load .nil .nil rfl (fun _ => 0) (fun _ h => by cases h)
example : ∃ cost, Load (CellIO.payload leaf) leaf leaf cost ∧ cost ≤ 56 :=
  Results.load leaf leaf rfl (CellIO.payload leaf) (fun _ _ => rfl)

end RotationBST.Tests.StreamingSnapshot
