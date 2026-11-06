module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Chocolate.Interruption.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Interruption.Results
open WeightedTree

theorem push_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree)
    (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, cs⟩ =
        some ⟨(stack.push new).decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, cs⟩ ∧
        ∀ x, (Tree.depth middle.tree x : ℝ) ≤
          Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x +
            6 + 14 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.push_prefix valid new cs

theorem pop_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, cs⟩ = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
        ∀ x, (Tree.depth middle.tree x : ℝ) ≤
          Tree.depth (Pointer.plug cs stack.decode.tree) x +
            6 + 10 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.pop_prefix valid popped cs

theorem uniform_pop_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest))
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ x, x < stack.decode.tree.size → (Tree.depth middle.tree x : ℝ) <
          13 + 17 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.uniform_pop_prefix valid popped unitWeights empty

theorem uniform_push_prefix {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node .nil stack.decode.tree, []⟩ =
        some ⟨(stack.push (.leaf .nil 1)).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node .nil stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push (.leaf .nil 1)).decode.tree, []⟩ ∧
        ∀ x, x < stack.decode.tree.size + 1 → (Tree.depth middle.tree x : ℝ) <
          14 + 21 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.uniform_push_prefix valid unitWeights empty

theorem pop_payload_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size → (Tree.depth middle.tree (offset + x) : ℝ) ≤
            Tree.depth subtree x + 13 + 7 * Real.logb 2 (stack.decode.mass / weight) +
              10 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.pop_payload_prefix valid popped

theorem push_payload_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, []⟩ =
        some ⟨(stack.push new).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size →
            (Tree.depth middle.tree (offset + new.tree.size + 1 + x) : ℝ) ≤
              Tree.depth subtree x + 14 + 7 * Real.logb 2 (stack.decode.mass / weight) +
                14 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.Interruption.push_payload_prefix valid new

theorem push_within (stack : Layer) (new : WeightedTree) :
    Pointer.TraceWithin (fun t => t.size = (Tree.node new.tree stack.decode.tree).size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth (.node new.tree stack.decode.tree) x + 8)
      ⟨.node new.tree stack.decode.tree, []⟩ ⟨(stack.push new).decode.tree, []⟩ stack.pushCost :=
  RotationBST.PopTart.Chocolate.Interruption.push_within stack new

theorem pop_within {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
      ∀ x, Tree.depth t x ≤ 4 * Tree.depth stack.decode.tree x + 8)
      ⟨stack.decode.tree, []⟩ ⟨.node crumb.tree rest.decode.tree, []⟩ stack.popCost :=
  RotationBST.PopTart.Chocolate.Interruption.pop_within popped

theorem push_depth_prefix (stack : Layer) (new : WeightedTree) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, cs⟩ = some ⟨(stack.push new).decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, cs⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤
          4 * Tree.depth (Pointer.plug cs (.node new.tree stack.decode.tree)) x + 8 :=
  RotationBST.PopTart.Chocolate.Interruption.push_depth_prefix stack new cs

theorem pop_depth_prefix {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) (cs : List Pointer.Frame) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, cs⟩ = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, cs⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, cs⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤
          4 * Tree.depth (Pointer.plug cs stack.decode.tree) x + 8 :=
  RotationBST.PopTart.Chocolate.Interruption.pop_depth_prefix popped cs

theorem pop_weighted_prefix {stack rest : Layer} {crumb : WeightedTree} (valid : stack.Valid 0)
    (popped : stack.pop = some (crumb, rest)) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.popCost ∧
      Multifinger.replay ops ⟨stack.decode.tree, []⟩ = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨.node crumb.tree rest.decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size → (Tree.depth middle.tree (offset + x) : ℝ) ≤
            4 * Tree.depth subtree x + 36 + 28 * Real.logb 2 (stack.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.Interruption.pop_weighted_prefix valid popped

theorem push_weighted_prefix {stack : Layer} (valid : stack.Valid 0) (new : WeightedTree) :
    ∃ ops : List Multifinger.Opcode, ops.length = stack.pushCost ∧
      Multifinger.replay ops ⟨.node new.tree stack.decode.tree, []⟩ = some ⟨(stack.push new).decode.tree, []⟩ ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (ops.take cut) ⟨.node new.tree stack.decode.tree, []⟩ = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some ⟨(stack.push new).decode.tree, []⟩ ∧
        ∀ subtree weight offset slotDepth,
          LocatedSlot stack.decode subtree weight offset slotDepth → 0 < weight →
          ∀ x, x < subtree.size →
            (Tree.depth middle.tree (offset + new.tree.size + 1 + x) : ℝ) ≤
              4 * Tree.depth subtree x + 40 + 28 * Real.logb 2 (stack.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.Interruption.push_weighted_prefix valid new

end RotationBST.PopTart.Chocolate.Interruption.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Chocolate.Interruption.Results`: 12 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Chocolate.Interruption.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract]
