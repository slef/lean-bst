module

public import RotationBST.Classical.Static.Definitions.Abstract

@[expose] public section

/-! Rank-balanced trees (Haeupler, Sen and Tarjan): each node stores an integer
rank and a missing child has rank `-1`. The rank difference of a child is its
parent's rank minus its own. One rule per classical structure. -/
namespace RotationBST.Classical.RankBalanced

/-- A tree with an integer rank in each node. -/
abbrev RankedTree := LabelledTree Int

/-- The rank of the root; `-1` for the empty tree. -/
def rank : RankedTree → Int
  | .nil => -1
  | .node _ k _ => k

/-- The balance rules. -/
inductive Rule where
  | avl
  | redBlack
  | wavl
  deriving DecidableEq, Repr

/-- No child of the root has rank difference zero. -/
def NoZeroChild : RankedTree → Prop
  | .nil => True
  | .node l k r => k - rank l ≠ 0 ∧ k - rank r ≠ 0

/-- The rule at one node of rank `k` with children `l` and `r`:
* AVL: the node is 1,1 or 1,2;
* red-black: rank differences are 0 or 1, and a 0-child has no 0-child;
* WAVL: rank differences are 1 or 2, and a leaf has rank 0. -/
def Rule.Local : Rule → RankedTree → Int → RankedTree → Prop
  | .avl, l, k, r =>
      (k - rank l = 1 ∧ k - rank r = 1) ∨ (k - rank l = 1 ∧ k - rank r = 2) ∨
        (k - rank l = 2 ∧ k - rank r = 1)
  | .redBlack, l, k, r =>
      (k - rank l = 0 ∨ k - rank l = 1) ∧ (k - rank r = 0 ∨ k - rank r = 1) ∧
        (k - rank l = 0 → NoZeroChild l) ∧ (k - rank r = 0 → NoZeroChild r)
  | .wavl, l, k, r =>
      (k - rank l = 1 ∨ k - rank l = 2) ∧ (k - rank r = 1 ∨ k - rank r = 2) ∧
        (l = .nil → r = .nil → k = 0)

/-- Every rank is nonnegative and every node satisfies the rule. -/
def Valid (rule : Rule) : RankedTree → Prop
  | .nil => True
  | .node l k r => 0 ≤ k ∧ rule.Local l k r ∧ Valid rule l ∧ Valid rule r

end RotationBST.Classical.RankBalanced
