module

public import RotationBST.Structures.PopTart.Cherry.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.CherryWeighted
open RotationBST.PopTart
open Cherry WeightedTree

private def leaf (w : ℝ) : WeightedTree := .leaf .nil w
private def bottom := leaf 0
private def one : Layers := .one (leaf 1) .nil
private def two : Layers := .two (leaf 2) (leaf 1) .nil
private def three : Layers := .three (leaf 3) (leaf 2) (leaf 1) .nil
private def four : Layers := .two (leaf 4) (leaf 3) (.one (.node (leaf 2) (leaf 1)) .nil)
private def afterPop : Layers := .one (leaf 3) (.one (.node (leaf 2) (leaf 1)) .nil)

private theorem fourValid : Valid 0 four :=
  .two (.leaf _ _) (.leaf _ _) (.one (.node (.leaf _ _) (.leaf _ _)) (.nil _))
private theorem fourOrdered : (four.decode bottom).Ordered := by
  norm_num [four, bottom, leaf, Layers.decode, Ordered, Nonnegative, fringe]

-- Unequal weights survive a carry, including the zero-weight bottom slot.
example : (four.decode bottom).mass = 10 := by norm_num [four, bottom, leaf, Layers.decode, mass]
example : (4 : ℝ) ≤ 3 + 4 * Real.logb 2 10 := by
  have slot : SlotAt (four.decode bottom) .nil 1 4 :=
    .right (.right (.left (.right (.leaf _ _))))
  have result := Cherry.Results.weighted_depth fourValid (.leaf _ _) fourOrdered slot (by norm_num)
  norm_num [four, bottom, leaf, Layers.decode, mass] at result ⊢
  exact result

-- The rank certificate identifies an occurrence, even though all its payload
-- shapes agree and the bottom has zero weight.
example : ∃ before after, (four.decode bottom).fringe = before ++ (Tree.nil, (1 : ℝ)) :: after ∧
    (4 : ℝ) ≤ 3 + 4 * Real.logb 2 ((before.length + 1 : Nat) : ℝ) := by
  have slot : SlotAt (four.decode bottom) .nil 1 4 :=
    .right (.right (.left (.right (.leaf _ _))))
  simpa only [bottom, leaf, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero] using
    Cherry.Results.depth_rank fourValid (.leaf _ _) slot

private def mixed : Program 0 .nil two 6 :=
  .cons (.push .nil (leaf 1) (.leaf _ _))
    (.cons (.push one (leaf 2) (.leaf _ _))
      (.cons (.push two (leaf 3) (.leaf _ _))
        (.cons (.push three (leaf 4) (.leaf _ _))
          (.cons (.pop four afterPop (leaf 4) rfl)
            (.cons (.pop afterPop two (leaf 3) rfl) (.nil two))))))

private theorem mixedIncreasing : mixed.Increasing bottom := by
  norm_num [mixed, Program.Increasing, Operation.Increasing, one, two, three, four,
    afterPop, bottom, leaf, Layers.push, Layers.decode, Ordered, Nonnegative, fringe]

example : mixed.cost = 16 := rfl
example : Valid 0 two ∧ (two.decode bottom).Ordered ∧ mixed.Realizes bottom ∧ 6 + mixed.cost ≤ 66 ∧
    ∀ subtree weight depth, SlotAt (two.decode bottom) subtree weight depth → 0 < weight →
      (depth : ℝ) ≤ 3 + 4 * Real.logb 2 ((two.decode bottom).mass / weight) :=
  Cherry.Results.weighted_sequence mixed (.leaf _ _) (by norm_num [bottom, leaf, Nonnegative]) mixedIncreasing

-- The condition is individual domination, not Vanilla's domination of total
-- old mass: pushing weight 2 above weights 2 and 1 remains ordered.
example : ((two.push (leaf 2)).decode bottom).Ordered := by
  apply Cherry.Results.push_leaf_ordered
  · norm_num [two, bottom, leaf, Layers.decode, Ordered, Nonnegative, fringe]
  · norm_num
  · norm_num [two, bottom, leaf, Layers.decode, fringe]

example : ¬ ((two.push (leaf 1)).decode bottom).Ordered := by
  norm_num [two, bottom, leaf, Layers.push, Layers.decode, Ordered, Nonnegative, fringe]

-- A positive frozen fringe above a zero bottom has W/w = 1. Its root still
-- lies at depth one, so the displayed bound without an additive term fails.
private def frozen : WeightedTree := .leaf (.node .nil .nil) 4
private def frozenStack : Layers := .one frozen .nil
private theorem frozenOrdered : (frozenStack.decode bottom).Ordered := by
  norm_num [frozenStack, frozen, bottom, leaf, Layers.decode, Ordered, Nonnegative, fringe]

example : ∃ cs : List Pointer.Frame, cs.length = 1 ∧
    Pointer.plug cs (.node .nil .nil) = (frozenStack.decode bottom).tree ∧
    Pointer.Trace ⟨(frozenStack.decode bottom).tree, []⟩ ⟨.node .nil .nil, cs⟩ 1 ∧
    (1 : ℝ) ≤ 3 + 4 * Real.logb 2 ((frozenStack.decode bottom).mass / 4) := by
  have slot : SlotAt (frozenStack.decode bottom) (.node .nil .nil) 4 1 := .left (.leaf _ _)
  simpa only [frozenStack, frozen, bottom, leaf, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero] using Cherry.Results.weighted_access
    (.one (.leaf _ _) (.nil _)) (.leaf _ _) frozenOrdered slot (by norm_num) (by intro h; cases h)

example : ¬ ((1 : ℝ) ≤ 4 * Real.logb 2 (4 / 4)) := by norm_num

-- Zero queried weights are intentionally outside the logarithmic conclusion,
-- while the empty zero-weight stack is a legal initialization.
example : (Layers.nil.decode bottom).Ordered := by
  norm_num [bottom, leaf, Layers.decode, Ordered, Nonnegative, fringe]

end RotationBST.Tests.CherryWeighted
