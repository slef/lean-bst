module

public import RotationBST.Structures.PopTart.Chocolate.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ChocolatePopTart
open RotationBST.PopTart
open Chocolate WeightedTree

private def leaf (w : ℝ) : WeightedTree := .leaf .nil w
private def pair (a b : ℝ) : WeightedTree := .node (leaf a) (leaf b)
private theorem leafPerfect (w : ℝ) : Perfect 0 (leaf w) := .leaf _ _
private theorem pairPerfect (a b : ℝ) : Perfect 1 (pair a b) := .node (leafPerfect a) (leafPerfect b)
private theorem leafGood (w : ℝ) (nonnegative : 0 ≤ w) : Perfect 0 (leaf w) ∧ (leaf w).Nonnegative :=
  ⟨leafPerfect w, nonnegative⟩

private def terminal (w : ℝ) : Layer :=
  .last (.three (leaf 1) (leaf 2) (leaf 3)) (.base (leaf w))
private theorem terminalValid (w : ℝ) (nonnegative : 0 ≤ w) : (terminal w).Valid 0 :=
  ⟨⟨leafGood 1 (by norm_num), leafGood 2 (by norm_num), leafGood 3 (by norm_num)⟩,
    leafGood w nonnegative, by intro h; cases h⟩

-- Terminal overflow creates a next layer when its mass is strictly smaller.
example : (terminal 10).push (leaf 0) =
    .next (.two (leaf 0) (leaf 1)) (.last .zero (.base (pair 2 3))) (.base (leaf 10)) := by
  norm_num [terminal, leaf, pair, Layer.push, Icing.decode, mass]

-- Equality freezes, so no active child can violate strict thick icing.
example : (terminal 5).push (leaf 0) =
    .last (.two (leaf 0) (leaf 1)) (.solid (pair 2 3) (.base (leaf 5))) := by
  norm_num [terminal, leaf, pair, Layer.push, Icing.decode, mass]
example : (terminal 5).pushCost = 6 := rfl
example : ((terminal 5).push (leaf 0)).Valid 0 :=
  (Chocolate.Results.push (terminalValid 5 (by norm_num)) (leafPerfect 0) (by norm_num [leaf, Nonnegative]) []).1

private def child : Layer := .last .zero (.base (pair 1 1))
private theorem childValid : child.Valid 1 :=
  ⟨trivial, ⟨pairPerfect 1 1, by norm_num [pair, leaf, Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩
private def active (w : ℝ) : Layer := .next (.three (leaf 1) (leaf 2) (leaf 3)) child (.base (leaf w))
private theorem activeValid (w : ℝ) (thick : 2 < w) : (active w).Valid 0 :=
  ⟨⟨leafGood 1 (by norm_num), leafGood 2 (by norm_num), leafGood 3 (by norm_num)⟩,
    childValid, leafGood w (by linarith), (by intro h; cases h),
    by simpa only [child, Layer.decode, Regulars.attach, Icing.decode, pair, leaf, mass,
      show (1 : ℝ) + 1 = 2 by norm_num] using thick⟩

example : (active 7).push (leaf 0) =
    .last (.two (leaf 0) (leaf 1)) (.frozen (pair 2 3) child (.base (leaf 7))) := by
  norm_num [active, child, leaf, pair, Layer.push, Layer.decode, Regulars.attach, Icing.decode, mass]
example : (active 7).pushCost = 8 := by
  norm_num [active, child, leaf, pair, Layer.pushCost, Layer.decode, Regulars.attach, Icing.decode, mass]
example : (active 8).pushCost = 14 := by
  norm_num [active, child, leaf, pair, Layer.pushCost, Layer.decode, Regulars.attach, Icing.decode, mass]

example (cs : List Pointer.Frame) :
    Pointer.Trace ⟨.node (leaf 0).tree (active 7).decode.tree, cs⟩
      ⟨((active 7).push (leaf 0)).decode.tree, cs⟩ 8 := by
  have trace := (Chocolate.Results.push (activeValid 7 (by norm_num)) (leafPerfect 0)
    (by norm_num [leaf, Nonnegative]) cs).2.2.2.1
  norm_num [active, child, leaf, pair, Layer.pushCost, Layer.decode, Regulars.attach, Icing.decode, mass] at trace ⊢
  exact trace

-- A carry continues into a full child and rebalances there too.
private def deepChild : Layer :=
  .last (.three (pair 1 1) (pair 1 1) (pair 1 1)) (.base (pair 50 50))
private def deep : Layer := .next (.three (leaf 1) (leaf 2) (leaf 3)) deepChild (.base (leaf 200))
example : deep.pushCost = 20 := by
  norm_num [deep, deepChild, leaf, pair, Layer.pushCost, Layer.decode, Regulars.attach, Icing.decode, mass]
example : Pointer.Trace ⟨.node (leaf 0).tree deep.decode.tree, []⟩
    ⟨(deep.push (leaf 0)).decode.tree, []⟩ 20 := by
  have trace := Chocolate.Results.push_trace deep (leaf 0)
  norm_num [deep, deepChild, leaf, pair, Layer.pushCost, Layer.decode, Regulars.attach, Icing.decode, mass] at trace ⊢
  exact trace

-- Nonmonotone weights are legal; these four pushes freeze the final carry.
private def start : Layer := .last .zero (.base (leaf 2))
private noncomputable def s1 := start.push (leaf 4)
private noncomputable def s2 := s1.push (leaf 1)
private noncomputable def s3 := s2.push (leaf 7)
private noncomputable def s4 := s3.push (leaf 0)
private noncomputable def program : Pushes 0 start s4 4 :=
  .cons (leaf 4) (leafPerfect 4) (by norm_num [leaf, Nonnegative])
    (.cons (leaf 1) (leafPerfect 1) (by norm_num [leaf, Nonnegative])
      (.cons (leaf 7) (leafPerfect 7) (by norm_num [leaf, Nonnegative])
        (.cons (leaf 0) (leafPerfect 0) (by norm_num [leaf, Nonnegative]) (.nil s4))))
example : program.cost = 6 := by
  norm_num [program, Pushes.cost, s1, s2, s3, start, Layer.pushCost, Layer.push, leaf,
    Layer.decode, Icing.decode, Regulars.attach, mass]
example : s4.Valid 0 ∧ program.Realizes ∧ 4 + program.cost ≤ 84 :=
  Chocolate.Results.empty_push_sequence program (leafPerfect 2) (by norm_num [leaf, Nonnegative])
example : s4.decode.fringe = [(Tree.nil, 0), (Tree.nil, 7), (Tree.nil, 1), (Tree.nil, 4), (Tree.nil, 2)] := by
  norm_num [s4, s3, s2, s1, start, Layer.push, Layer.decode, Icing.decode, Regulars.attach, fringe, leaf, mass]

-- Icing collapse retains the exact tree and mass of a frozen pending carry.
private def ice : Icing := .frozen (pair 2 3) child (.base (leaf 7))
private theorem iceValid : ice.Valid 0 := by
  refine ⟨pairPerfect 2 3, ?_, childValid, leafGood 7 (by norm_num), ?_, ?_⟩
  all_goals norm_num [child, pair, leaf, Nonnegative, Layer.decode, Icing.decode, Regulars.attach, mass]
example : ice.outer.tree = ice.decode.tree := Chocolate.Results.outer_tree ice
example : ice.outer.mass = ice.decode.mass := Chocolate.Results.outer_mass ice
example : Vanilla.Valid ice.outer := Chocolate.Results.icing_vanilla iceValid

private def block : WeightedTree := .node (pair 2 3) child.decode
example : ∃ cs : List Pointer.Frame, cs.length = 1 ∧ Pointer.plug cs block.tree = ice.decode.tree ∧
    Pointer.Trace ⟨ice.decode.tree, []⟩ ⟨block.tree, cs⟩ 1 ∧
    (1 : ℝ) ≤ 1 + Real.logb 2 (ice.decode.mass / block.mass) := by
  have slot : SlotAt ice.outer block.tree block.mass 1 := .left (.leaf _ _)
  simpa only [Nat.cast_one] using Chocolate.Results.icing_access iceValid slot
    (by norm_num [block, pair, child, leaf, mass, Layer.decode, Icing.decode, Regulars.attach])
    (by intro h; cases h)

-- Arbitrary ordering does not permit negative weights or a non-base empty layer.
example : ¬ (Layer.last .zero (.base (leaf (-1)))).Valid 0 := by
  simp [Layer.Valid, Icing.Valid, Regulars.Valid, leaf, Nonnegative]
example : ¬ (Layer.last .zero (.solid (pair 2 3) (.base (leaf 5)))).Valid 0 := by
  simp [Layer.Valid]

end RotationBST.Tests.ChocolatePopTart
