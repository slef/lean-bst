module

public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Interruption.Abstract
public import RotationBST.Structures.PopTart.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ChocolateDepth
open RotationBST.PopTart
open Chocolate WeightedTree

private def leaf (w : ℝ) : WeightedTree := .leaf .nil w
private def pair : WeightedTree := .node (leaf 1) (leaf 1)
private def small : Layer := .last .zero (.base pair)
private theorem leafPerfect (w : ℝ) : Perfect 0 (leaf w) := .leaf _ _
private theorem pairPerfect : Perfect 1 pair := .node (leafPerfect 1) (leafPerfect 1)
private theorem leafGood (w : ℝ) (positive : 0 ≤ w) : Perfect 0 (leaf w) ∧ (leaf w).Nonnegative :=
  ⟨leafPerfect w, positive⟩
private theorem smallValid : small.Valid 1 :=
  ⟨trivial, ⟨pairPerfect, by norm_num [pair, leaf, Nonnegative]⟩, fun _ => ⟨_, rfl⟩⟩

private def carry (payload : Tree) : WeightedTree := .node (leaf 1) (.leaf payload 1000)
private def ice (payload : Tree) : Icing := .frozen (carry payload) small (.base (leaf 3))
private def stack (payload : Tree) : Layer :=
  .next (.three (leaf 1) (leaf 1) (leaf 1)) small (ice payload)

private theorem iceValid (payload : Tree) : (ice payload).Valid 0 := by
  refine ⟨.node (leafPerfect 1) (.leaf _ _), ?_, smallValid, leafGood 3 (by norm_num), ?_, ?_⟩
  all_goals norm_num [small, carry, pair, leaf, Nonnegative, Layer.decode, Regulars.attach, Icing.decode, mass]
private theorem stackValid (payload : Tree) : (stack payload).Valid 0 := by
  refine ⟨⟨leafGood 1 (by norm_num), leafGood 1 (by norm_num), leafGood 1 (by norm_num)⟩,
    smallValid, iceValid payload, (by intro h; cases h), ?_⟩
  norm_num [small, ice, carry, pair, leaf, Layer.decode, Regulars.attach, Icing.decode, mass]
private theorem stackMass (payload : Tree) : (stack payload).decode.mass = 1011 := by
  norm_num [stack, small, ice, carry, pair, leaf, Layer.decode, Regulars.attach, Icing.decode, mass]
private theorem heavySlot (payload : Tree) : SlotAt (stack payload).decode payload 1000 7 :=
  .right (.right (.right (.right (.left (.left (.right (.leaf _ _)))))))

-- This positive-weight boundary tree is produced by nine ordinary pushes.
-- Its heavy leaf lies below three regular nodes, a next node, an icing node,
-- the frozen pending carry root, and one crumb edge.
private noncomputable def build (weights : List ℝ) : Layer :=
  weights.foldl (fun state w => state.push (leaf w)) (.last .zero (.base (leaf 3)))
example : build [1, 1, 1000, 1, 1, 1, 1, 1, 1] = stack .nil := by
  norm_num [build, List.foldl, Layer.push, stack, small, ice, carry, pair, leaf,
    Layer.decode, Regulars.attach, Icing.decode, mass]
example : ∀ p ∈ (stack .nil).decode.fringe, 0 < p.2 := by
  norm_num [stack, small, ice, carry, pair, leaf, Layer.decode, Regulars.attach, Icing.decode, fringe]

-- The literal additive six is too small for this reachable configuration.
example : ¬ ((7 : ℝ) ≤ 6 + 7 * Real.logb 2 ((stack .nil).decode.mass / 1000)) := by
  rw [stackMass]
  have logarithm := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by norm_num : 0 < ((1011 : ℝ) / 1000) ^ 7)
    (by norm_num : ((1011 : ℝ) / 1000) ^ 7 < 2)
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), Nat.cast_ofNat] at logarithm
  linarith only [logarithm]

example : (7 : ℝ) ≤ 7 + 7 * Real.logb 2 ((stack .nil).decode.mass / 1000) := by
  simpa only [Nat.cast_ofNat] using Chocolate.Results.weighted_depth (stackValid .nil) (heavySlot .nil) (by norm_num)

-- The same bound reaches an actual nonempty payload through frozen icing.
example : ∃ cs : List Pointer.Frame, cs.length = 7 ∧
    Pointer.plug cs (.node .nil .nil) = (stack (.node .nil .nil)).decode.tree ∧
    Pointer.Trace ⟨(stack (.node .nil .nil)).decode.tree, []⟩ ⟨.node .nil .nil, cs⟩ 7 ∧
    (7 : ℝ) ≤ 7 + 7 * Real.logb 2 ((stack (.node .nil .nil)).decode.mass / 1000) := by
  simpa only [Nat.cast_ofNat] using Chocolate.Results.weighted_access
    (stackValid (.node .nil .nil)) (heavySlot (.node .nil .nil)) (by norm_num) (by intro h; cases h)

example : (1 + (stack .nil).pushCost : ℝ) ≤ 7 + 14 * Real.logb 2 ((stack .nil).decode.leafCount) :=
  Chocolate.Results.push_worst_case (stackValid .nil)

-- Leaves in the saved old layer use the historical thick-icing inequality.
example : (7 : ℝ) ≤ 7 + 7 * Real.logb 2 ((stack .nil).decode.mass / 1) := by
  have slot : SlotAt (stack .nil).decode .nil 1 7 :=
    .right (.right (.right (.right (.left (.right (.left (.leaf _ _)))))))
  simpa only [Nat.cast_ofNat, Nat.cast_one] using
    Chocolate.Results.weighted_depth (stackValid .nil) slot (by norm_num)

-- Unit weights recover ordinary height and key search depths.
private def uniformIce : Icing := .solid pair (.base (leaf 1))
private def uniform : Layer := .next (.three (leaf 1) (leaf 1) (leaf 1)) small uniformIce
private theorem uniformValid : uniform.Valid 0 := by
  refine ⟨⟨leafGood 1 (by norm_num), leafGood 1 (by norm_num), leafGood 1 (by norm_num)⟩,
    smallValid, ⟨pairPerfect, ?_, leafGood 1 (by norm_num), ?_⟩, (by intro h; cases h), ?_⟩
  all_goals norm_num [uniformIce, small, pair, leaf, Nonnegative, Layer.decode, Regulars.attach, Icing.decode, mass]
private theorem uniformWeights : ∀ subtree weight depth, SlotAt uniform.decode subtree weight depth → weight = 1 := by
  intro subtree weight depth slot
  obtain ⟨before, after, split⟩ := WeightedTree.Results.slot_split slot
  have mem : (subtree, weight) ∈ uniform.decode.fringe := by rw [split]; simp
  have weights : ∀ p ∈ uniform.decode.fringe, p.2 = 1 := by
    norm_num [uniform, uniformIce, small, pair, leaf, Layer.decode, Regulars.attach, Icing.decode, fringe]
  exact weights _ mem

example : (uniform.decode.height : ℝ) ≤ 7 + 7 * Real.logb 2 8 := by
  simpa only [show uniform.decode.leafCount = 8 by rfl, Nat.cast_ofNat] using
    Chocolate.Results.uniform_height uniformValid uniformWeights
example (x : Nat) (inside : x < uniform.decode.tree.size) :
    (Tree.depth uniform.decode.tree x : ℝ) < 7 + 7 * Real.logb 2 8 := by
  have empty : uniform.decode.EmptyFringe := by repeat constructor
  simpa only [show uniform.decode.tree.size + 1 = 8 by rfl, Nat.cast_ofNat] using
    Chocolate.Results.uniform_key_depth uniformValid uniformWeights empty x inside

-- A singleton positive fringe has no active transitions and zero depth.
example (w : ℝ) (positive : 0 < w) :
    (0 : ℝ) ≤ 7 + 7 * Real.logb 2 ((Layer.last .zero (.base (leaf w))).decode.mass / w) := by
  have valid : (Layer.last .zero (.base (leaf w))).Valid 0 :=
    ⟨trivial, leafGood w positive.le, fun _ => ⟨_, rfl⟩⟩
  simpa only [Nat.cast_zero] using Chocolate.Results.weighted_depth valid (.leaf _ _) positive

-- Unit-weight stacks have logarithmic depth throughout physical push, not
-- just after its final rotation. Here the old fringe contains eight leaves.
example : ∃ ops : List Multifinger.Opcode, ops.length = uniform.pushCost ∧
    Multifinger.replay ops ⟨.node .nil uniform.decode.tree, []⟩ =
      some ⟨(uniform.push (.leaf .nil 1)).decode.tree, []⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨.node .nil uniform.decode.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨(uniform.push (.leaf .nil 1)).decode.tree, []⟩ ∧
      ∀ x, x < uniform.decode.tree.size + 1 → (Tree.depth middle.tree x : ℝ) <
        14 + 21 * Real.logb 2 uniform.decode.leafCount := by
  apply Chocolate.Interruption.Results.uniform_push_prefix uniformValid uniformWeights
  simp [uniform, uniformIce, small, pair, leaf, Layer.decode, Regulars.attach, Icing.decode, EmptyFringe]

-- A heavy nonempty payload remains at its exact shifted rank at every cut
-- of a recursive carry. Its local depth is zero; its weight is 1000.
example : ∃ ops : List Multifinger.Opcode,
    ops.length = (stack (.node .nil .nil)).pushCost ∧
    Multifinger.replay ops ⟨.node .nil (stack (.node .nil .nil)).decode.tree, []⟩ =
      some ⟨((stack (.node .nil .nil)).push (leaf 1)).decode.tree, []⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨.node .nil (stack (.node .nil .nil)).decode.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle =
        some ⟨((stack (.node .nil .nil)).push (leaf 1)).decode.tree, []⟩ ∧
      (Tree.depth middle.tree 7 : ℝ) ≤ 14 + 7 * Real.logb 2 (1011 / 1000) + 14 * Real.logb 2 10 := by
  obtain ⟨ops, length, replay, prefixes⟩ := Chocolate.Interruption.Results.push_payload_prefix
    (stackValid (.node .nil .nil)) (leaf 1)
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  have slot : LocatedSlot (stack (.node .nil .nil)).decode (.node .nil .nil) 1000 6 7 :=
    .right (.right (.right (.right (.left (.left (.right (.leaf _ _)))))))
  have bound := bounds _ _ _ _ slot (by norm_num) 0 (by simp [Tree.size])
  refine ⟨middle, first, last, ?_⟩
  simpa only [stackMass, show (stack (.node .nil .nil)).decode.leafCount = 10 from rfl,
    leaf, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
    Tree.size, Nat.add_zero, Tree.depth, Nat.lt_irrefl, ite_false, ite_true,
    Nat.cast_zero, zero_add, Nat.cast_ofNat] using bound

-- The same recursive carry now has a weighted-only interruption bound.
-- Its heavy frozen payload remains at rank seven without a leaf-count term.
example : ∃ ops : List Multifinger.Opcode,
    ops.length = (stack (.node .nil .nil)).pushCost ∧
    Multifinger.replay ops ⟨.node .nil (stack (.node .nil .nil)).decode.tree, []⟩ =
      some ⟨((stack (.node .nil .nil)).push (leaf 1)).decode.tree, []⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨.node .nil (stack (.node .nil .nil)).decode.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle =
        some ⟨((stack (.node .nil .nil)).push (leaf 1)).decode.tree, []⟩ ∧
      (Tree.depth middle.tree 7 : ℝ) ≤ 40 + 28 * Real.logb 2 (1011 / 1000) := by
  obtain ⟨ops, length, replay, prefixes⟩ := Chocolate.Interruption.Results.push_weighted_prefix
    (stackValid (.node .nil .nil)) (leaf 1)
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  have slot : LocatedSlot (stack (.node .nil .nil)).decode (.node .nil .nil) 1000 6 7 :=
    .right (.right (.right (.right (.left (.left (.right (.leaf _ _)))))))
  have bound := bounds _ _ _ _ slot (by norm_num) 0 (by simp [Tree.size])
  refine ⟨middle, first, last, ?_⟩
  simpa only [stackMass,
    leaf, WeightedTree.tree, WeightedTree.skeleton, Pointer.Lazy.Skeleton.tree,
    Tree.size, Nat.add_zero, Tree.depth, Nat.lt_irrefl, ite_false, ite_true,
    Nat.cast_zero, zero_add, mul_zero, Nat.cast_ofNat] using bound

-- Thawing a frozen heavy payload has the same purely weighted guarantee at
-- every cut of the six actual instructions, including its original rank.
private def heavyThaw : Layer := .last (.one (leaf 1)) (ice (.node .nil .nil))
private def heavyThawed : Layer :=
  .next (.two (leaf 1) (.leaf (.node .nil .nil) 1000)) small (.base (leaf 3))
private theorem heavyThawValid : heavyThaw.Valid 0 :=
  ⟨leafGood 1 (by norm_num), iceValid _, by intro h; cases h⟩
example : ∃ ops : List Multifinger.Opcode, ops.length = 6 ∧
    Multifinger.replay ops ⟨heavyThaw.decode.tree, []⟩ = some ⟨.node .nil heavyThawed.decode.tree, []⟩ ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (ops.take cut) ⟨heavyThaw.decode.tree, []⟩ = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some ⟨.node .nil heavyThawed.decode.tree, []⟩ ∧
      (Tree.depth middle.tree 2 : ℝ) ≤ 36 + 28 * Real.logb 2 (1007 / 1000) := by
  obtain ⟨ops, length, replay, prefixes⟩ := Chocolate.Interruption.Results.pop_weighted_prefix
    heavyThawValid (rest := heavyThawed) (crumb := leaf 1) rfl
  refine ⟨ops, length, replay, ?_⟩
  intro cut
  obtain ⟨middle, first, last, bounds⟩ := prefixes cut
  have slot : LocatedSlot heavyThaw.decode (.node .nil .nil) 1000 2 4 :=
    .right (.left (.left (.right (.leaf _ _))))
  have bound := bounds _ _ _ _ slot (by norm_num) 0 (by simp [Tree.size])
  refine ⟨middle, first, last, ?_⟩
  have massEq : heavyThaw.decode.mass = 1007 := by
    norm_num [heavyThaw, ice, carry, small, pair, leaf, Layer.decode, Icing.decode, Regulars.attach, mass]
  simpa only [massEq, Nat.add_zero, Tree.depth, Tree.size, Nat.lt_irrefl,
    ite_false, ite_true, Nat.cast_zero, mul_zero, zero_add] using bound

end RotationBST.Tests.ChocolateDepth
