module

public import RotationBST.Classical.RankBalanced.Definitions.Abstract

@[expose] public section

/-! Bottom-up insertion into rank-balanced trees under the WAVL rule, which is
also AVL insertion (Haeupler, Sen and Tarjan). The new leaf has rank 0. Going
up, a parent with a 0-child is promoted if its other child is a 1-child;
otherwise one single or double rotation, with the promotions and demotions it
needs, ends the rebalancing. Each function returns the tree, the number of
rotations and the number of rank changes. -/
namespace RotationBST.Classical.RankBalanced

/-- The tree with a new leaf of rank 0 at gap `g`, before rebalancing. -/
def leafAt : RankedTree → Nat → RankedTree
  | .nil, _ => .node .nil 0 .nil
  | .node l k r, g =>
      if g ≤ l.erase.size then .node (leafAt l g) k r
      else .node l k (leafAt r (g - l.erase.size - 1))

/-- Rebalance a node of rank `k` whose left subtree became `l'`. -/
def fixLeft (l' : RankedTree) (k : Int) (r : RankedTree) (a e : Nat) : RankedTree × Nat × Nat :=
  if k - rank l' ≠ 0 then (.node l' k r, a, e)
  else if k - rank r = 1 then (.node l' (k + 1) r, a, e + 1)
  else
    match l' with
    | .node x kx y =>
        if kx - rank x = 1 then (.node x kx (.node y (k - 1) r), a + 1, e + 1)
        else
          match y with
          | .node y₁ _ y₂ => (.node (.node x (k - 1) y₁) k (.node y₂ (k - 1) r), a + 2, e + 3)
          | .nil => (.node l' k r, a, e)
    | .nil => (.node l' k r, a, e)

/-- Rebalance a node of rank `k` whose right subtree became `r'`. -/
def fixRight (l : RankedTree) (k : Int) (r' : RankedTree) (a e : Nat) : RankedTree × Nat × Nat :=
  if k - rank r' ≠ 0 then (.node l k r', a, e)
  else if k - rank l = 1 then (.node l (k + 1) r', a, e + 1)
  else
    match r' with
    | .node y ky z =>
        if ky - rank z = 1 then (.node (.node l (k - 1) y) ky z, a + 1, e + 1)
        else
          match y with
          | .node y₁ _ y₂ => (.node (.node l (k - 1) y₁) k (.node y₂ (k - 1) z), a + 2, e + 3)
          | .nil => (.node l k r', a, e)
    | .nil => (.node l k r', a, e)

/-- Insert at gap `g` and rebalance: (tree, rotations, rank changes). -/
def insert : RankedTree → Nat → RankedTree × Nat × Nat
  | .nil, _ => (.node .nil 0 .nil, 0, 0)
  | .node l k r, g =>
      if g ≤ l.erase.size then
        let p := insert l g
        fixLeft p.1 k r p.2.1 p.2.2
      else
        let p := insert r (g - l.erase.size - 1)
        fixRight l k p.1 p.2.1 p.2.2

/-- Insert the gaps of a list one after the other. -/
def insertAll (t : RankedTree) : List Nat → RankedTree
  | [] => t
  | g :: gs => insertAll (insert t g).1 gs

/-- The total number of rank changes of a sequence of insertions. -/
def insertEdits (t : RankedTree) : List Nat → Nat
  | [] => 0
  | g :: gs => (insert t g).2.2 + insertEdits (insert t g).1 gs

end RotationBST.Classical.RankBalanced
