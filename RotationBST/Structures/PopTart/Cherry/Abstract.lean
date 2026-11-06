module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Cherry.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Cherry.Results
open WeightedTree

theorem push {level : Nat} {layers : Layers} (valid : Valid level layers)
    {crumb : WeightedTree} (perfect : Perfect level crumb) (bottom : WeightedTree) :
    Valid level (layers.push crumb) ∧
      ((layers.push crumb).decode bottom).fringe = crumb.fringe ++ (layers.decode bottom).fringe ∧
      Pointer.Trace ⟨.node crumb.tree (layers.decode bottom).tree, []⟩
        ⟨((layers.push crumb).decode bottom).tree, []⟩ layers.pushCost ∧
      layers.pushCost + (layers.push crumb).potential ≤ 10 + layers.potential :=
  RotationBST.PopTart.Cherry.push valid perfect bottom

theorem pop {level : Nat} {layers : Layers} (valid : Valid level layers) (nonempty : layers ≠ .nil)
    (bottom : WeightedTree) :
    ∃ crumb rest, layers.pop = some (crumb, rest) ∧ Perfect level crumb ∧ Valid level rest ∧
      (layers.decode bottom).fringe = crumb.fringe ++ (rest.decode bottom).fringe ∧
      Pointer.Trace ⟨(layers.decode bottom).tree, []⟩
        ⟨.node crumb.tree (rest.decode bottom).tree, []⟩ layers.popCost ∧
      layers.popCost + rest.potential ≤ 10 + layers.potential :=
  RotationBST.PopTart.Cherry.pop valid nonempty bottom

theorem operation_trace {level : Nat} {layers rest : Layers}
    (op : Operation level layers rest) (bottom : WeightedTree) (cs : List Pointer.Frame) :
    Pointer.Trace ⟨op.input bottom, cs⟩ ⟨op.output bottom, cs⟩ op.cost :=
  RotationBST.PopTart.Cherry.operation_trace op bottom cs

theorem sequence {level : Nat} {layers rest : Layers} {n : Nat}
    (program : Program level layers rest n) (valid : Valid level layers) (bottom : WeightedTree) :
    Valid level rest ∧ program.Realizes bottom ∧ program.cost + rest.potential ≤ 10 * n + layers.potential :=
  RotationBST.PopTart.Cherry.sequence program valid bottom

theorem empty_sequence {level : Nat} {rest : Layers} {n : Nat}
    (program : Program level .nil rest n) (bottom : WeightedTree) :
    Valid level rest ∧ program.Realizes bottom ∧ n + program.cost ≤ 11 * n :=
  RotationBST.PopTart.Cherry.empty_sequence program bottom

theorem layer_population {level : Nat} {layers : Layers} (valid : Valid level layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    2 ^ (level + layers.height) + 1 ≤ leafCount (layers.decode bottom) + 2 ^ level :=
  RotationBST.PopTart.Cherry.layer_population valid base

theorem height_log {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    (layers.height : ℝ) ≤ Real.logb 2 (leafCount (layers.decode bottom)) :=
  RotationBST.PopTart.Cherry.height_log valid base

theorem depth_log {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    (depth : ℝ) ≤ 4 * Real.logb 2 (leafCount (layers.decode bottom)) :=
  RotationBST.PopTart.Cherry.depth_log valid base slot

theorem key_depth {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) (empty : (layers.decode bottom).EmptyFringe)
    (x : Nat) (inside : x < (layers.decode bottom).tree.size) :
    (Tree.depth (layers.decode bottom).tree x : ℝ) <
      4 * Real.logb 2 (((layers.decode bottom).tree.size + 1 : Nat) : ℝ) :=
  RotationBST.PopTart.Cherry.key_depth valid base empty x inside

theorem worst_case {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom) :
    (layers.pushCost : ℝ) ≤ 10 * Real.logb 2 (leafCount (layers.decode bottom)) ∧
      (layers.popCost : ℝ) ≤ 6 * Real.logb 2 (leafCount (layers.decode bottom)) :=
  RotationBST.PopTart.Cherry.worst_case valid base

theorem depth_rank {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) :
    ∃ before after, (layers.decode bottom).fringe = before ++ (subtree, weight) :: after ∧
      (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((before.length + 1 : Nat) : ℝ) :=
  RotationBST.PopTart.Cherry.depth_rank valid base slot

theorem push_ordered {layers : Layers} {crumb bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (newOrdered : crumb.Ordered)
    (dominates : ∀ a ∈ crumb.fringe, ∀ b ∈ (layers.decode bottom).fringe, b.2 ≤ a.2) :
    ((layers.push crumb).decode bottom).Ordered :=
  RotationBST.PopTart.Cherry.push_ordered ordered newOrdered dominates

theorem push_leaf_ordered {layers : Layers} {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (subtree : Tree) (weight : ℝ)
    (nonnegative : 0 ≤ weight)
    (dominates : ∀ b ∈ (layers.decode bottom).fringe, b.2 ≤ weight) :
    ((layers.push (.leaf subtree weight)).decode bottom).Ordered :=
  RotationBST.PopTart.Cherry.push_leaf_ordered ordered subtree weight nonnegative dominates

theorem pop_ordered {layers rest : Layers} {crumb bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (popped : layers.pop = some (crumb, rest)) :
    crumb.Ordered ∧ (rest.decode bottom).Ordered :=
  RotationBST.PopTart.Cherry.pop_ordered ordered popped

theorem operation_ordered {level : Nat} {layers rest : Layers}
    (op : Operation level layers rest) {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (increasing : op.Increasing bottom) :
    (rest.decode bottom).Ordered :=
  RotationBST.PopTart.Cherry.operation_ordered op ordered increasing

theorem sequence_ordered {level : Nat} {layers rest : Layers} {n : Nat}
    (program : Program level layers rest n) {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (increasing : program.Increasing bottom) :
    (rest.decode bottom).Ordered :=
  RotationBST.PopTart.Cherry.sequence_ordered program ordered increasing

theorem weighted_depth {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    (ordered : (layers.decode bottom).Ordered)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) (positive : 0 < weight) :
    (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((layers.decode bottom).mass / weight) :=
  RotationBST.PopTart.Cherry.weighted_depth valid base ordered slot positive

theorem weighted_access {layers : Layers} (valid : Valid 0 layers)
    {bottom : WeightedTree} (base : Perfect 0 bottom)
    (ordered : (layers.decode bottom).Ordered)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt (layers.decode bottom) subtree weight depth) (positive : 0 < weight)
    (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = (layers.decode bottom).tree ∧
      Pointer.Trace ⟨(layers.decode bottom).tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((layers.decode bottom).mass / weight) :=
  RotationBST.PopTart.Cherry.weighted_access valid base ordered slot positive nonempty

theorem weighted_sequence {rest : Layers} {n : Nat} (program : Program 0 .nil rest n)
    {bottom : WeightedTree} (base : Perfect 0 bottom) (bottomNonnegative : bottom.Nonnegative)
    (increasing : program.Increasing bottom) :
    Valid 0 rest ∧ (rest.decode bottom).Ordered ∧ program.Realizes bottom ∧ n + program.cost ≤ 11 * n ∧
      ∀ subtree weight depth, SlotAt (rest.decode bottom) subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((rest.decode bottom).mass / weight) :=
  RotationBST.PopTart.Cherry.weighted_sequence program base bottomNonnegative increasing

end RotationBST.PopTart.Cherry.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Cherry.Results`: 19 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Cherry.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Cherry.Definitions.Abstract]
