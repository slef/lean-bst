module

public import RotationBST.Structures.PopTart.Located.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.LocatedPopTart
open PopTart PopTart.WeightedTree

private def payload : Tree := .node .nil .nil
private def duplicate : WeightedTree :=
  .node (.leaf payload 4) (.node (.leaf payload 4) (.leaf .nil 0))

private theorem first : LocatedSlot duplicate payload 4 0 1 := .left (.leaf _ _)
private theorem second : LocatedSlot duplicate payload 4 2 2 := .right (.left (.leaf _ _))
private theorem last : LocatedSlot duplicate .nil 0 4 2 := .right (.right (.leaf _ _))

-- Identical shape/weight pairs have different ranks and different depths.
example : ∃ depth, LocatedSlot duplicate payload 4 2 depth := by
  have slot := Located.Results.locate_split
    (show duplicate.fringe = [(payload, 4)] ++ (payload, 4) :: [(.nil, 0)] from rfl)
  norm_num only [fringeSpan, payload, Tree.size, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil] at slot
  exact slot

example : Tree.depth duplicate.tree 0 = 1 := by
  have equation := Located.Results.key_depth first 0 (by decide)
  simpa [payload, Tree.depth, Tree.size] using equation

example : Tree.depth duplicate.tree 2 = 2 := by
  have equation := Located.Results.key_depth second 0 (by decide)
  simpa [payload, Tree.depth, Tree.size] using equation

example : ∃ cs : List Pointer.Frame,
    cs.length = 2 ∧ Pointer.offset cs = 2 ∧ Pointer.plug cs payload = duplicate.tree :=
  Located.Results.context second

-- The predecessor and successor separators are actual ancestors of this
-- occurrence, not keys guessed from an equal-shaped payload elsewhere.
example : Tree.depth duplicate.tree 1 < 2 :=
  Located.Results.predecessor_depth second (by decide)

example : Tree.depth duplicate.tree 3 < 2 :=
  Located.Results.successor_depth second (by decide)

-- Empty external slots still bound their adjacent separator. The final
-- external slot has no successor in this tree, and the first has no predecessor.
example : Tree.depth duplicate.tree 3 < 2 :=
  Located.Results.predecessor_depth last (by decide)

example : ¬ 4 + Tree.nil.size < duplicate.tree.size := by decide
example : ¬ 0 < (0 : Nat) := by decide

example : ∃ before after, duplicate.fringe = before ++ (payload, 4) :: after ∧
    fringeSpan before = 2 := Located.Results.split second

end RotationBST.Tests.LocatedPopTart
