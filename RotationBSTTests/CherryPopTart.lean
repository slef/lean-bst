module

public import RotationBST.Structures.PopTart.Cherry.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.CherryPopTart
open RotationBST.PopTart
open Cherry WeightedTree

private def unit : WeightedTree := .leaf .nil 1
private def pair : WeightedTree := .node unit unit
private def quad : WeightedTree := .node pair pair
private theorem unitPerfect : Perfect 0 unit := .leaf .nil 1
private theorem pairPerfect : Perfect 1 pair := .node unitPerfect unitPerfect
private theorem quadPerfect : Perfect 2 quad := .node pairPerfect pairPerfect

private def one : Layers := .one unit .nil
private def two : Layers := .two unit unit .nil
private def three : Layers := .three unit unit unit .nil
private def four : Layers := .two unit unit (.one pair .nil)
private def afterOnePop : Layers := .one unit (.one pair .nil)

-- Four pushes carry the last two level-zero crumbs into level one.
example : three.push unit = four := rfl
example : three.pushCost = 10 := rfl
example : four.pop = some (unit, afterOnePop) := rfl
example : afterOnePop.pop = some (unit, two) := rfl
example : afterOnePop.popCost = 6 := rfl

private theorem threeValid : Valid 0 three :=
  .three unitPerfect unitPerfect unitPerfect (.nil _)
private theorem fourValid : Valid 0 four :=
  (Cherry.Results.push threeValid unitPerfect unit).1

example : Pointer.Trace ⟨.node unit.tree (three.decode unit).tree, []⟩
    ⟨(four.decode unit).tree, []⟩ 10 :=
  (Cherry.Results.push threeValid unitPerfect unit).2.2.1

-- Carries and borrows really propagate through multiple levels.
private def full : Layers := .three unit unit unit (.three pair pair pair .nil)
private theorem fullValid : Valid 0 full :=
  .three unitPerfect unitPerfect unitPerfect (.three pairPerfect pairPerfect pairPerfect (.nil _))
private def sparse : Layers := .one unit (.one pair (.one quad .nil))
private def borrowed : Layers := .two unit unit (.two pair pair .nil)
private theorem sparseValid : Valid 0 sparse :=
  .one unitPerfect (.one pairPerfect (.one quadPerfect (.nil _)))

example : full.push unit = .two unit unit (.two pair pair (.one quad .nil)) := rfl
example : full.pushCost = 20 := rfl
example : sparse.pop = some (unit, borrowed) := rfl
example : sparse.popCost = 12 := rfl

example (cs : List Pointer.Frame) :
    Pointer.Trace ⟨(sparse.decode unit).tree, cs⟩ ⟨.node unit.tree (borrowed.decode unit).tree, cs⟩ 12 :=
  Cherry.Results.operation_trace (.pop sparse borrowed unit rfl : Operation 0 sparse borrowed) unit cs

-- The complete six-operation mixed history has sixteen rebalancing moves,
-- and the generic theorem supplies every actual boundary trace and validity.
private def mixed : Program 0 .nil two 6 :=
  .cons (.push .nil unit unitPerfect)
    (.cons (.push one unit unitPerfect)
      (.cons (.push two unit unitPerfect)
        (.cons (.push three unit unitPerfect)
          (.cons (.pop four afterOnePop unit rfl)
            (.cons (.pop afterOnePop two unit rfl) (.nil two))))))

example : mixed.cost = 16 := rfl
example : Valid 0 two ∧ mixed.Realizes unit ∧ 6 + mixed.cost ≤ 66 :=
  Cherry.Results.empty_sequence mixed unit

-- Logarithmic depth applies to every actual key in the ordinary BST, not
-- just to the layer count. This tree has nine keys and ten external leaves.
example (x : Nat) (inside : x < (full.decode unit).tree.size) :
    (Tree.depth (full.decode unit).tree x : ℝ) < 4 * Real.logb 2 10 := by
  have empty : (full.decode unit).EmptyFringe := by repeat constructor
  simpa only [show (full.decode unit).tree.size + 1 = 10 by rfl, Nat.cast_ofNat] using
    Cherry.Results.key_depth fullValid unitPerfect empty x inside

example : (full.pushCost : ℝ) ≤ 10 * Real.logb 2 (leafCount (full.decode unit)) ∧
    (full.popCost : ℝ) ≤ 6 * Real.logb 2 (leafCount (full.decode unit)) :=
  Cherry.Results.worst_case fullValid unitPerfect

-- Merging crumbs preserves occurrence weights, even when all shapes agree.
example : (((Layers.three (.leaf .nil 3) (.leaf .nil 2) (.leaf .nil 1) .nil).push (.leaf .nil 4)).decode unit).fringe =
    [(Tree.nil, 4), (Tree.nil, 3), (Tree.nil, 2), (Tree.nil, 1), (Tree.nil, 1)] := rfl

-- Empty stacks and malformed next-level crumbs are distinguished.
example : Layers.nil.pop = none := rfl
example : one.pop = some (unit, .nil) := rfl
example : (Layers.one unit (.one unit .nil)).pop = none := rfl
example : ¬ Valid 0 (.one unit (.one unit .nil)) := by
  intro valid
  cases valid with
  | one head tail =>
    cases tail with
    | one bad rest => cases bad

end RotationBST.Tests.CherryPopTart
