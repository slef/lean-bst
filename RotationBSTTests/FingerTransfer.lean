module

public import RotationBST.Structures.HeavyPath.Finger.Transfer.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerTransfer
open HeavyPath HeavyPath.Finger PopTart PopTart.WeightedTree PopTart.Chocolate

private def leaf : Tree := .node .nil .nil
private def emptyStack : Layer := .last .zero (.base (.leaf .nil 0))
private def simple : Finger.Pair :=
  ⟨.last .zero (.base (.leaf (Tree.node leaf .nil).mirror 2)), emptyStack⟩
private def nested : Finger.Pair :=
  ⟨.last (.one (.leaf (Tree.node leaf .nil).mirror 3)) (.base (.leaf .nil 0)), emptyStack⟩

private theorem simpleValid : simple.Valid := by
  exact ⟨⟨trivial, ⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩,
    ⟨trivial, ⟨.leaf _ _, le_rfl⟩, fun _ => ⟨_, rfl⟩⟩⟩

private theorem nestedValid : nested.Valid := by
  exact ⟨⟨⟨.leaf _ _, by norm_num [WeightedTree.Nonnegative]⟩,
    ⟨.leaf _ _, le_rfl⟩, by intro h; cases h⟩, simpleValid.2⟩

-- With no intervening ancestor, two physical moves expose the new root,
-- followed by two moves into and out of the receiving stack.
example : Pointer.Trace ⟨simple.tree, []⟩ ⟨(simple.downLeft leaf .nil 1 1).tree, []⟩ 4 :=
  Transfer.Results.downLeft_trace (p := simple) (oldCharge := 2) rfl 1 1

example : (simple.downLeft leaf .nil 1 1).tree = .node leaf leaf := rfl

example : (simple.downLeft leaf .nil 1 1).Valid :=
  Transfer.Results.downLeft_valid simpleValid leaf .nil (by norm_num) (by norm_num)

-- An existing inverted-path separator requires the second rotation. No
-- separator node is inserted for free or lost from the fringe.
example : Pointer.Trace ⟨nested.tree, []⟩ ⟨(nested.downLeft leaf .nil 2 1).tree, []⟩ 6 :=
  Transfer.Results.downLeft_trace (p := nested) (oldCharge := 3) rfl 2 1

example : (Pointer.Config.mk (nested.downLeft leaf .nil 2 1).tree []).key? = some 2 := by
  have rank := Transfer.Results.downLeft_root_key (p := nested) (oldCharge := 3) rfl 2 1
  norm_num [nested, Layer.decode, Regulars.attach, Icing.decode, WeightedTree.tree,
    WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror, Tree.size, leaf] at rank
  exact rank

example : (nested.downLeft leaf .nil 2 1).mass = nested.mass := by
  have balance := Transfer.Results.downLeft_mass nestedValid (oldCharge := 3) rfl 2 (by norm_num : (0 : ℝ) ≤ 1)
  linarith

example : (nested.downLeft leaf .nil 2 1).lower.decode.mirror.fringe = [(.nil, 0), (leaf, 2)] ∧
    (nested.downLeft leaf .nil 2 1).upper.decode.fringe = [(.nil, 1), (.nil, 0)] := by
  norm_num [Pair.downLeft, nested, emptyStack, Layer.replaceTop, Layer.push, Layer.decode,
    Regulars.attach, Icing.decode, WeightedTree.mirror, WeightedTree.fringe, Tree.mirror_mirror, Tree.mirror]

-- Reflection yields the actual opposite-direction trace and the new rank.
example : Pointer.Trace ⟨simple.flip.tree, []⟩ ⟨(simple.flip.downRight .nil leaf 1 1).tree, []⟩ 4 :=
  Transfer.Results.downRight_trace (p := simple.flip) (oldCharge := 2) rfl 1 1

example : (Pointer.Config.mk (simple.flip.downRight .nil leaf 1 1).tree []).key? = some 1 :=
  Transfer.Results.downRight_root_key simple.flip .nil leaf 1 1

private def receiving : Layer :=
  .last (.three (.leaf .nil 1) (.leaf .nil 1) (.leaf .nil 1)) (.base (.leaf .nil 0))
private def carrying : Finger.Pair := ⟨simple.lower, receiving⟩

private theorem receivingValid : receiving.Valid 0 := by
  refine ⟨⟨⟨.leaf _ _, ?_⟩, ⟨.leaf _ _, ?_⟩, ⟨.leaf _ _, ?_⟩⟩,
    ⟨.leaf _ _, le_rfl⟩, ?_⟩
  all_goals simp [WeightedTree.Nonnegative]

private theorem carryingValid : carrying.Valid := ⟨simpleValid.1, receivingValid⟩

-- This push triggers Chocolate freezing and six rebalancing instructions.
example : carrying.downLeftCost = 10 := rfl

example : Pointer.Trace ⟨carrying.tree, []⟩ ⟨(carrying.downLeft leaf .nil 1 1).tree, []⟩ 10 :=
  Transfer.Results.downLeft_trace (p := carrying) (oldCharge := 2) rfl 1 1

example : carrying.downLeftCost + (carrying.downLeft leaf .nil 1 1).potential ≤ 26 + carrying.potential :=
  Transfer.Results.downLeft_amortized carryingValid leaf .nil 1 (by norm_num)

example : (carrying.downLeft leaf .nil 1 1).Valid :=
  Transfer.Results.downLeft_valid carryingValid leaf .nil (by norm_num) (by norm_num)

-- Replacing the active top leaf of a frozen stack preserves all stored
-- repair credit, including the untouched icing metadata.
example : ((receiving.push (.leaf .nil 1)).replaceTop (.leaf leaf 7)).potential =
    (receiving.push (.leaf .nil 1)).potential := by
  have valid := (Chocolate.Results.push receivingValid (.leaf .nil 1) (by norm_num [WeightedTree.Nonnegative]) []).1
  exact Chocolate.Top.Results.replaceTop_potential valid _

-- The replacement API lifts a supplied rotation trace; it does not create
-- a physical subtree change just from new metadata.
example : ∃ cost, cost ≤ 4 ∧ Pointer.Trace
    ⟨nested.lower.decode.tree, []⟩
    ⟨(nested.lower.replaceTop (.leaf (Tree.node leaf .nil) 3)).decode.tree, []⟩ cost := by
  apply Chocolate.Top.Results.replaceTop_lift nested.lower (.leaf (Tree.node leaf .nil) 3)
    (cost := 2) (by decide) (by decide)
  change Pointer.Trace ⟨.node .nil leaf, []⟩ ⟨.node leaf .nil, []⟩ 2
  exact .step .downRight (.step .rotateRightChild .refl)

end RotationBST.Tests.FingerTransfer
