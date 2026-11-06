module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Vanilla.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Vanilla.Results

theorem nonnegative {stack : WeightedTree} (valid : Valid stack) : stack.Nonnegative :=
  RotationBST.PopTart.Vanilla.nonnegative valid

theorem push_valid {stack : WeightedTree} (valid : Valid stack) (t : Tree) (w : ℝ)
    (dominates : stack.mass ≤ w) : Valid (push t w stack) :=
  RotationBST.PopTart.Vanilla.push_valid valid t w dominates

theorem pop_push (t : Tree) (w : ℝ) (stack : WeightedTree) :
    pop (push t w stack) = some ((t, w), stack) :=
  RotationBST.PopTart.Vanilla.pop_push t w stack

theorem pop_valid {stack tail : WeightedTree} {t : Tree} {w : ℝ}
    (valid : Valid stack) (exposed : pop stack = some ((t, w), tail)) :
    Valid tail ∧ 0 ≤ w ∧ tail.mass ≤ w :=
  RotationBST.PopTart.Vanilla.pop_valid valid exposed

theorem cases_valid {stack : WeightedTree} (valid : Valid stack) :
    (∃ t w, stack = .leaf t w ∧ 0 ≤ w) ∨
      ∃ t w tail, stack = push t w tail ∧ Valid tail ∧ tail.mass ≤ w :=
  RotationBST.PopTart.Vanilla.cases_valid valid

theorem depth_mass {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) :
    (2 : ℝ) ^ depth * weight ≤ 2 * stack.mass :=
  RotationBST.PopTart.Vanilla.depth_mass valid slot

theorem depth_log {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) (slotPositive : 0 < weight) :
    (depth : ℝ) ≤ 1 + Real.logb 2 (stack.mass / weight) :=
  RotationBST.PopTart.Vanilla.depth_log valid slot slotPositive

theorem access_slot {stack : WeightedTree} (valid : Valid stack)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : WeightedTree.SlotAt stack subtree weight depth) (slotPositive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = stack.tree ∧
      Pointer.Trace ⟨stack.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 1 + Real.logb 2 (stack.mass / weight) :=
  RotationBST.PopTart.Vanilla.access_slot valid slot slotPositive nonempty

theorem push_fringe (t : Tree) (w : ℝ) (stack : WeightedTree) :
    (push t w stack).skeleton.fringe = t :: stack.skeleton.fringe :=
  RotationBST.PopTart.Vanilla.push_fringe t w stack

theorem pop_fringe {stack tail : WeightedTree} {t : Tree} {w : ℝ}
    (exposed : pop stack = some ((t, w), tail)) :
    stack.skeleton.fringe = t :: tail.skeleton.fringe :=
  RotationBST.PopTart.Vanilla.pop_fringe exposed

theorem operation {stack tail : WeightedTree} (op : Operation stack tail) (cs : List Pointer.Frame) :
    Pointer.Trace ⟨op.input, cs⟩ ⟨op.output, cs⟩ 0 :=
  RotationBST.PopTart.Vanilla.operation op cs

end RotationBST.PopTart.Vanilla.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Vanilla.Results`: 11 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Vanilla.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Vanilla.Definitions.Abstract]
