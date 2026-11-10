module

public import RotationBST.Classical.RankBalanced.Insertion.Abstract
public import RotationBST.Classical.RankBalanced.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.RankInsertion
open Classical.RankBalanced

private def leaf : RankedTree := .node .nil 0 .nil

-- Increasing insertions: the second promotes the root; the third promotes the
-- new leaf's parent, then rotates once and demotes, ending with the perfect
-- tree of three keys.
example : Classical.RankBalanced.insert .nil 0 = (leaf, 0, 0) := by decide
example : Classical.RankBalanced.insert leaf 1 = (.node .nil 1 leaf, 0, 1) := by decide
example : Classical.RankBalanced.insert (.node .nil 1 leaf) 2 = (.node leaf 1 leaf, 1, 2) := by decide
-- A double rotation: insert between the root and its only child.
example : Classical.RankBalanced.insert (.node .nil 1 leaf) 1 = (.node leaf 1 leaf, 2, 4) := by decide


-- Insertions keep both rules, with at most two rotations each.
example (t : RankedTree) (g : Nat) (h : Valid .avl t) :
    Valid .avl (Classical.RankBalanced.insert t g).1 ∧ (Classical.RankBalanced.insert t g).2.1 ≤ 2 :=
  ⟨Results.insert_avl t g h, Results.insert_rotations t g ((avl_iff t).mp h).1⟩
example (gs : List Nat) : insertEdits .nil gs ≤ 7 * gs.length := Results.insertEdits_empty gs
example : insertEdits .nil [0, 1, 2] = 3 := by decide

end RotationBST.Tests.RankInsertion
