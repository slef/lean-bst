module

import RotationBST.Audit.Check
public import RotationBST.Models.Pointer.Detour.AbstractBridge

@[expose] public section
namespace RotationBST.Pointer.Detour.Results

theorem trace_nonempty {a b : Config} {cost : Nat} (trace : Trace a b cost)
    (live : a.focus ≠ .nil) : b.focus ≠ .nil :=
  RotationBST.Pointer.Detour.trace_nonempty trace live

theorem walk {start : Config} {current target : Nat}
    (key : start.key? = some current) (valid : target < start.tree.size) :
    ∃ (visited : Config) (cost : Nat), visited.key? = some target ∧ visited.tree = start.tree ∧
      Walk start visited cost ∧ Walk visited start cost ∧
      cost ≤ Tree.depth start.tree current + Tree.depth start.tree target ∧
      (current = target → cost = 0) :=
  RotationBST.Pointer.Detour.walk key valid

theorem record {a b : Config} {cost : Nat} (walk : Walk a b cost) :
    ∃ ops : List Multifinger.Opcode, ops.length = cost ∧ Multifinger.replay ops a = some b ∧
      ∀ cut, ∃ middle, Multifinger.replay (ops.take cut) a = some middle ∧ middle.tree = a.tree :=
  RotationBST.Pointer.Detour.record walk

theorem bounded {start : Config} (live : start.focus ≠ .nil) {target : Nat}
    (valid : target < start.tree.size) {height : ℝ}
    (depths : ∀ x < start.tree.size, (Tree.depth start.tree x : ℝ) ≤ height) :
    ∃ (visited : Config) (before after : List Multifinger.Opcode),
      Multifinger.replay before start = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some start ∧
      (1 + before.length + after.length : ℝ) ≤ 1 + 4 * height ∧
      (start.key? = some target → before = [] ∧ after = []) ∧
      (∀ cut, ∃ middle, Multifinger.replay (before.take cut) start = some middle ∧ middle.tree = start.tree) ∧
      (∀ cut, ∃ middle, Multifinger.replay (after.take cut) visited = some middle ∧ middle.tree = start.tree) :=
  RotationBST.Pointer.Detour.bounded live valid depths

theorem resume {start middle visited finish : Config}
    {earlier before after later : List Multifinger.Opcode}
    (first : Multifinger.replay earlier start = some middle)
    (outward : Multifinger.replay before middle = some visited)
    (backward : Multifinger.replay after visited = some middle)
    (last : Multifinger.replay later middle = some finish) :
    Multifinger.replay (earlier ++ before ++ after ++ later) start = some finish :=
  RotationBST.Pointer.Detour.resume first outward backward last

end RotationBST.Pointer.Detour.Results

/-- info: abstract audit passed for `RotationBST.Pointer.Detour.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Detour.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
