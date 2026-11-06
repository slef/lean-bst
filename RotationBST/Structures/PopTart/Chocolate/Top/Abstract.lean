module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Chocolate.Top.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Chocolate.Top.Results
open WeightedTree

theorem decode_top (stack : Layer) :
    stack.decode = stack.topTail.elim stack.top (WeightedTree.node stack.top) :=
  RotationBST.PopTart.Chocolate.decode_top stack

theorem replaceTop_decode (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode = stack.topTail.elim new (WeightedTree.node new) :=
  RotationBST.PopTart.Chocolate.replaceTop_decode stack new

theorem replaceTop_top (stack : Layer) (new : WeightedTree) : (stack.replaceTop new).top = new :=
  RotationBST.PopTart.Chocolate.replaceTop_top stack new

theorem replaceTop_tail (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).topTail = stack.topTail :=
  RotationBST.PopTart.Chocolate.replaceTop_tail stack new

theorem top_valid {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    Perfect level stack.top ∧ stack.top.Nonnegative :=
  RotationBST.PopTart.Chocolate.top_valid valid

theorem replaceTop_valid {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {new : WeightedTree} (perfect : Perfect level new) (nonnegative : new.Nonnegative) :
    (stack.replaceTop new).Valid level :=
  RotationBST.PopTart.Chocolate.replaceTop_valid valid perfect nonnegative

theorem replaceTop_potential {stack : Layer} {level : Nat} (valid : stack.Valid level) (new : WeightedTree) :
    (stack.replaceTop new).potential = stack.potential :=
  RotationBST.PopTart.Chocolate.replaceTop_potential valid new

theorem replaceTop_mass (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode.mass + stack.top.mass = stack.decode.mass + new.mass :=
  RotationBST.PopTart.Chocolate.replaceTop_mass stack new

theorem replaceTop_size (stack : Layer) (new : WeightedTree) :
    (stack.replaceTop new).decode.tree.size + stack.top.tree.size = stack.decode.tree.size + new.tree.size :=
  RotationBST.PopTart.Chocolate.replaceTop_size stack new

theorem replaceTop_lift (stack : Layer) (new : WeightedTree) {cost : Nat}
    (oldNonempty : stack.top.tree ≠ .nil) (newNonempty : new.tree ≠ .nil)
    (trace : Pointer.Trace ⟨stack.top.tree, []⟩ ⟨new.tree, []⟩ cost) :
    ∃ total, total ≤ cost + 2 ∧
      Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨(stack.replaceTop new).decode.tree, []⟩ total :=
  RotationBST.PopTart.Chocolate.replaceTop_lift stack new oldNonempty newNonempty trace

theorem hasTop_of_fringe {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {suffix : List (Tree × ℝ)}
    (fringe : stack.decode.fringe = (subtree, weight) :: suffix) (nonempty : suffix ≠ []) :
    stack.HasTop :=
  RotationBST.PopTart.Chocolate.hasTop_of_fringe valid fringe nonempty

theorem pop_front {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {suffix : List (Tree × ℝ)}
    (fringe : stack.decode.fringe = (subtree, weight) :: suffix) (nonempty : suffix ≠ []) :
    ∃ rest, stack.pop = some (.leaf subtree weight, rest) ∧ rest.Valid 0 ∧
      rest.decode.fringe = suffix ∧ stack.decode.mass = weight + rest.decode.mass ∧
      stack.popCost + rest.potential ≤ 20 + stack.potential :=
  RotationBST.PopTart.Chocolate.pop_front valid fringe nonempty

theorem replaceTop_replaceTop (stack : Layer) (first second : WeightedTree) :
    (stack.replaceTop first).replaceTop second = stack.replaceTop second :=
  RotationBST.PopTart.Chocolate.replaceTop_replaceTop stack first second

theorem replaceTop_within (stack : Layer) (new : WeightedTree) {cost factor constant : Nat}
    (factorPositive : 1 ≤ factor)
    (oldNonempty : stack.top.tree ≠ .nil) (newNonempty : new.tree ≠ .nil)
    (trace : Pointer.TraceWithin (fun t => t.size = stack.top.tree.size ∧
      ∀ x, Tree.depth t x ≤ factor * Tree.depth stack.top.tree x + constant)
      ⟨stack.top.tree, []⟩ ⟨new.tree, []⟩ cost) :
    ∃ total, total ≤ cost + 2 ∧
      Pointer.TraceWithin (fun t => t.size = stack.decode.tree.size ∧
        ∀ x, Tree.depth t x ≤ factor * Tree.depth stack.decode.tree x + constant)
        ⟨stack.decode.tree, []⟩ ⟨(stack.replaceTop new).decode.tree, []⟩ total :=
  RotationBST.PopTart.Chocolate.replaceTop_within stack new factorPositive oldNonempty newNonempty trace

end RotationBST.PopTart.Chocolate.Top.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Chocolate.Top.Results`: 14 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Chocolate.Top.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract]
