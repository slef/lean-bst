module

public import RotationBST.Structures.PopTart.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

/-- Each preceding payload contributes its keys and the separator following
it. The final fringe has no following separator in the physical tree. -/
def fringeSpan (slots : List (Tree × ℝ)) : Nat :=
  (slots.map (fun p => p.1.size + 1)).sum

/-- An outer fringe occurrence with both its physical inorder offset and its
outer edge depth. Equal-shaped, equal-weight payloads remain distinct by rank. -/
inductive LocatedSlot : WeightedTree → Tree → ℝ → Nat → Nat → Prop where
  | leaf (t : Tree) (w : ℝ) : LocatedSlot (.leaf t w) t w 0 0
  | left {l r : WeightedTree} {t : Tree} {w : ℝ} {offset depth : Nat} :
      LocatedSlot l t w offset depth → LocatedSlot (.node l r) t w offset (depth + 1)
  | right {l r : WeightedTree} {t : Tree} {w : ℝ} {offset depth : Nat} :
      LocatedSlot r t w offset depth →
        LocatedSlot (.node l r) t w (offset + l.tree.size + 1) (depth + 1)

end RotationBST.PopTart.WeightedTree
