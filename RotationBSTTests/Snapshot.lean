module

public import RotationBST.Structures.TreeBuffer.Snapshot.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.Snapshot
open Multifinger TreeBuffer.Snapshot

private def leaf : Tree := .node .nil .nil
private def leftThree : Tree := .node (.node leaf .nil) .nil
private def rightThree : Tree := .node .nil (.node .nil leaf)

-- The log contains movement and rotation opcodes, not target-tree nodes.
example : record leftThree = [.downLeft, .rotateLeftChild, .downLeft, .rotateLeftChild,
    .downRight, .downRight, .upRight, .upRight] := by decide
example : replay (record leftThree) ⟨leftThree, []⟩ = some ⟨rightThree, []⟩ := by decide
example : encodedCells leftThree = [1800, 1584, 0] := by decide
example : decodeCells [1800, 1584, 0] = record leftThree := by decide

-- Arbitrary same-size current trees can be restored from just the packed data.
example : replay (loadEncoded rightThree [1800, 1584, 0]) ⟨rightThree, []⟩ = some ⟨leftThree, []⟩ := by decide
example : (loadEncoded rightThree [1800, 1584, 0]).length = 16 := by decide
example : (saveProgram leftThree).length = 20 := by decide
example : Pointer.Trace ⟨leftThree, []⟩ ⟨leftThree, []⟩ (saveProgram leftThree).length :=
  (Results.save leftThree).1
example : Pointer.Trace ⟨rightThree, []⟩ ⟨leftThree, []⟩ (loadProgram rightThree (record leftThree)).length :=
  (Results.load rightThree leftThree (by decide)).1

-- Context is restored as well as shape. A subtree snapshot does not destroy
-- the surrounding tree or leave the cursor at the canonical vine's root.
example : replay (loadEncoded rightThree (encodedCells leftThree)) ⟨rightThree, [.right leaf]⟩ =
    some ⟨leftThree, [.right leaf]⟩ :=
  (Results.encoded_restore rightThree leftThree (by decide) [.right leaf]).1

-- Rotation reversal needs navigation: swapping rotation names alone is illegal
-- from the promoted node. The three-instruction inverse restores its old cursor.
private def before : Pointer.Config := ⟨leaf, [.left leaf]⟩
private def after : Pointer.Config := ⟨.node .nil (.node .nil leaf), []⟩
example : perform .rotateLeftChild before = some after := by decide
example : perform .rotateRightChild after = none := by decide
example : replay Opcode.rotateLeftChild.inverse after = some before :=
  inverse_replay (op := .rotateLeftChild) (by decide)
example : replay [.downLeft] ⟨.nil, []⟩ = none := by decide

-- Four digits, including rotations, fit in the checked payload bound.
example : decodeCell (encodeCell [.rotateRightChild, .upLeft, .downRight, .rotateLeftChild]) =
    [.rotateRightChild, .upLeft, .downRight, .rotateLeftChild] := by decide
example : ∀ code ∈ encodedCells leftThree, code < 4096 := (Results.storage leftThree).2.1
example : (encodedCells rightThree).length = 3 := (Results.storage rightThree).1
example : record leftThree ≠ record rightThree := by decide

-- The normalizer's local controller emits the same stream and halts at the
-- canonical tree. All legal prefixes keep its only counter within the universe.
example : Controller.Run ⟨⟨leftThree, []⟩, 0, .scan⟩ (record leftThree)
    ⟨⟨rightThree, []⟩, 0, .ascend⟩ := Controller.Results.normalizes leftThree
example : Controller.tick ⟨⟨leftThree, []⟩, 0, .scan⟩ =
    some (some .downLeft, ⟨⟨.node leaf .nil, [.left .nil]⟩, 0, .promote⟩) := by decide
example : Controller.tick ⟨⟨rightThree, []⟩, 0, .ascend⟩ = none := Controller.Results.halts leftThree
example (s : Controller.State) (ops : List Opcode)
    (run : Controller.Run ⟨⟨leftThree, []⟩, 0, .scan⟩ ops s) : s.depth ≤ 3 :=
  Controller.Results.counter leftThree run

-- Empty and singleton snapshots need no pointer instructions; packet padding
-- still gives exactly one payload slot per existing node.
example : encodedCells .nil = [] := by decide
example : encodedCells leaf = [0] := by decide
example : saveProgram .nil = [] ∧ saveProgram leaf = [] := by decide
example : replay (loadEncoded .nil []) ⟨.nil, []⟩ = some ⟨.nil, []⟩ := by decide
example : Controller.Run ⟨⟨.nil, []⟩, 0, .scan⟩ [] ⟨⟨.nil, []⟩, 0, .ascend⟩ :=
  Controller.Results.normalizes .nil

end RotationBST.Tests.Snapshot
