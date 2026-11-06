module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Window.AbstractBridge

@[expose] public section
namespace RotationBST.Deamortization.Window.Results
open Pointer

theorem serve {start finish : Config} {ops : List Multifinger.Opcode}
    (executed : Multifinger.replay ops start = some finish) (live : start.focus ≠ .nil)
    {target budget : Nat} (valid : target < start.tree.size)
    (visits : ∃ cut visited, cut ≤ ops.length ∧
      Multifinger.replay (ops.take cut) start = some visited ∧ visited.key? = some target)
    (height : ∀ cut middle, Multifinger.replay (ops.take cut) start = some middle →
      ∀ x < middle.tree.size, Tree.depth middle.tree x ≤ budget) :
    ∃ (consumed : Nat) (middle visited : Config) (before after : List Multifinger.Opcode),
      consumed ≤ budget ∧ consumed ≤ ops.length ∧
      Multifinger.replay (ops.take consumed) start = some middle ∧
      Multifinger.replay (ops.drop consumed) middle = some finish ∧
      Multifinger.replay before start = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some middle ∧
      before.length + after.length ≤ 5 * consumed ∧
      1 + before.length + after.length ≤ 1 + 5 * budget ∧
      (consumed = budget ∨ middle.key? = some target) :=
  RotationBST.Deamortization.Window.serve executed live valid visits height

end RotationBST.Deamortization.Window.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Window.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Window.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
