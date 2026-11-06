module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Chocolate.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Results
open WeightedTree

theorem layer_nonnegative {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    stack.decode.Nonnegative :=
  RotationBST.PopTart.Chocolate.layer_nonnegative valid

theorem icing_nonnegative {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    icing.decode.Nonnegative :=
  RotationBST.PopTart.Chocolate.icing_nonnegative valid

theorem push {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {new : WeightedTree} (perfect : Perfect level new) (nonnegative : new.Nonnegative)
    (cs : List Pointer.Frame) :
    (stack.push new).Valid level ∧
      (stack.push new).decode.fringe = new.fringe ++ stack.decode.fringe ∧
      (stack.push new).decode.mass = new.mass + stack.decode.mass ∧
      Pointer.Trace ⟨.node new.tree stack.decode.tree, cs⟩
        ⟨(stack.push new).decode.tree, cs⟩ stack.pushCost ∧
      stack.pushCost + (stack.push new).potential ≤ 20 + stack.potential :=
  RotationBST.PopTart.Chocolate.push valid perfect nonnegative cs

theorem push_trace (stack : Layer) (new : WeightedTree) :
    Pointer.Trace ⟨.node new.tree stack.decode.tree, []⟩
      ⟨(stack.push new).decode.tree, []⟩ stack.pushCost :=
  RotationBST.PopTart.Chocolate.push_trace stack new

theorem push_sequence {level : Nat} {stack rest : Layer} {n : Nat}
    (program : Pushes level stack rest n) (valid : stack.Valid level) :
    rest.Valid level ∧ program.Realizes ∧ program.cost + rest.potential ≤ 20 * n + stack.potential :=
  RotationBST.PopTart.Chocolate.push_sequence program valid

theorem empty_push_sequence {level : Nat} {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Pushes level (.last .zero (.base bottom)) rest n)
    (base : Perfect level bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid level ∧ program.Realizes ∧ n + program.cost ≤ 21 * n :=
  RotationBST.PopTart.Chocolate.empty_push_sequence program base nonnegative

theorem outer_tree (icing : Icing) : icing.outer.tree = icing.decode.tree :=
  RotationBST.PopTart.Chocolate.outer_tree icing

theorem outer_mass (icing : Icing) : icing.outer.mass = icing.decode.mass :=
  RotationBST.PopTart.Chocolate.outer_mass icing

theorem icing_vanilla {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    Vanilla.Valid icing.outer :=
  RotationBST.PopTart.Chocolate.icing_vanilla valid

theorem icing_depth {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.outer subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 1 + Real.logb 2 (icing.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.icing_depth valid slot positive

theorem icing_access {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.outer subtree weight depth) (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = icing.decode.tree ∧
      Pointer.Trace ⟨icing.decode.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 1 + Real.logb 2 (icing.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.icing_access valid slot positive nonempty

theorem layer_depth {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ (level : ℝ) + 7 + 7 * Real.logb 2 (stack.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.layer_depth valid slot positive

theorem icing_leaf_depth {icing : Icing} {level : Nat} (valid : icing.Valid level)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt icing.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ (level : ℝ) + 3 + 7 * Real.logb 2 (icing.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.icing_leaf_depth valid slot positive

theorem weighted_depth {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.weighted_depth valid slot positive

theorem weighted_access {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = stack.decode.tree ∧
      Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.weighted_access valid slot positive nonempty

theorem weighted_push_sequence {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Pushes 0 (.last .zero (.base bottom)) rest n)
    (base : Perfect 0 bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid 0 ∧ program.Realizes ∧ n + program.cost ≤ 21 * n ∧
      ∀ subtree weight depth, SlotAt rest.decode subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (rest.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.weighted_push_sequence program base nonnegative

theorem icing_population {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    2 ^ level ≤ icing.decode.leafCount :=
  RotationBST.PopTart.Chocolate.icing_population valid

theorem active_population {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    2 ^ (level + stack.activeDepth) ≤ stack.decode.leafCount :=
  RotationBST.PopTart.Chocolate.active_population valid

theorem push_cost_active_depth (stack : Layer) : stack.pushCost ≤ 14 * stack.activeDepth + 6 :=
  RotationBST.PopTart.Chocolate.push_cost_active_depth stack

theorem push_worst_case {stack : Layer} (valid : stack.Valid 0) :
    (1 + stack.pushCost : ℝ) ≤ 7 + 14 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.push_worst_case valid

theorem uniform_height {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1) :
    (stack.decode.height : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.uniform_height valid unitWeights

theorem uniform_key_depth {stack : Layer} (valid : stack.Valid 0)
    (unitWeights : ∀ subtree weight depth, SlotAt stack.decode subtree weight depth → weight = 1)
    (empty : stack.decode.EmptyFringe) (x : Nat) (inside : x < stack.decode.tree.size) :
    (Tree.depth stack.decode.tree x : ℝ) <
      7 + 7 * Real.logb 2 (((stack.decode.tree.size + 1 : Nat) : ℝ)) :=
  RotationBST.PopTart.Chocolate.uniform_key_depth valid unitWeights empty x inside

theorem pop {stack : Layer} {level : Nat} (valid : stack.Valid level) (top : stack.HasTop)
    (cs : List Pointer.Frame) :
    ∃ crumb rest, stack.pop = some (crumb, rest) ∧ Perfect level crumb ∧ crumb.Nonnegative ∧ rest.Valid level ∧
      stack.decode.fringe = crumb.fringe ++ rest.decode.fringe ∧
      stack.decode.mass = crumb.mass + rest.decode.mass ∧
      Pointer.Trace ⟨stack.decode.tree, cs⟩ ⟨.node crumb.tree rest.decode.tree, cs⟩ stack.popCost ∧
      stack.popCost + rest.potential ≤ 20 + stack.potential :=
  RotationBST.PopTart.Chocolate.pop valid top cs

theorem pop_trace {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨.node crumb.tree rest.decode.tree, []⟩ stack.popCost :=
  RotationBST.PopTart.Chocolate.pop_trace popped

theorem pop_worst_case {stack : Layer} (valid : stack.Valid 0) :
    (1 + stack.popCost : ℝ) ≤ 7 + 10 * Real.logb 2 (stack.decode.leafCount) :=
  RotationBST.PopTart.Chocolate.pop_worst_case valid

theorem operation_valid {level : Nat} {stack rest : Layer} (valid : stack.Valid level)
    (op : Operation level stack rest) : rest.Valid level :=
  RotationBST.PopTart.Chocolate.operation_valid valid op

theorem operation_trace {level : Nat} {stack rest : Layer} (op : Operation level stack rest)
    (cs : List Pointer.Frame) : Pointer.Trace ⟨op.input, cs⟩ ⟨op.output, cs⟩ op.cost :=
  RotationBST.PopTart.Chocolate.operation_trace op cs

theorem operation_amortized {level : Nat} {stack rest : Layer} (op : Operation level stack rest) :
    op.cost + rest.potential ≤ 20 + stack.potential :=
  RotationBST.PopTart.Chocolate.operation_amortized op

theorem operation_worst_case {stack rest : Layer} (valid : stack.Valid 0)
    (op : Operation 0 stack rest) :
    (1 + op.cost : ℝ) ≤ 7 + 14 * Real.logb 2 stack.decode.leafCount :=
  RotationBST.PopTart.Chocolate.operation_worst_case valid op

theorem sequence {level : Nat} {stack rest : Layer} {n : Nat}
    (program : Program level stack rest n) (valid : stack.Valid level) :
    rest.Valid level ∧ program.Realizes ∧ program.cost + rest.potential ≤ 20 * n + stack.potential :=
  RotationBST.PopTart.Chocolate.sequence program valid

theorem empty_sequence {level : Nat} {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Program level (.last .zero (.base bottom)) rest n)
    (base : Perfect level bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid level ∧ program.Realizes ∧ n + program.cost ≤ 21 * n :=
  RotationBST.PopTart.Chocolate.empty_sequence program base nonnegative

theorem weighted_sequence {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Program 0 (.last .zero (.base bottom)) rest n)
    (base : Perfect 0 bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid 0 ∧ program.Realizes ∧ n + program.cost ≤ 21 * n ∧
      ∀ subtree weight depth, SlotAt rest.decode subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (rest.decode.mass / weight) :=
  RotationBST.PopTart.Chocolate.weighted_sequence program base nonnegative

theorem layer_potential_bound (stack : Layer) :
    stack.potential + 20 ≤ 20 * stack.decode.leafCount :=
  RotationBST.PopTart.Chocolate.layer_potential_bound stack

theorem icing_potential_bound (icing : Icing) :
    icing.potential + 20 ≤ 20 * icing.decode.leafCount :=
  RotationBST.PopTart.Chocolate.icing_potential_bound icing

end RotationBST.PopTart.Chocolate.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Chocolate.Results`: 34 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Chocolate.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Vanilla.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract]
