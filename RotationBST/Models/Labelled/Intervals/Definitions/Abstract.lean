module

public import RotationBST.Models.Labelled.Metadata.Definitions.Abstract

@[expose] public section
namespace RotationBST.IntervalMetadata

structure Bounds where
  low : Nat
  high : Nat
  deriving DecidableEq

/-- Finite node fields describing the interval of each rooted subtree. The
recursive annotation is the representation invariant, not the routing code. -/
def label : Tree → Nat → LabelledTree (Nat × Bounds)
  | .nil, _ => .nil
  | .node l r, lo => .node (label l lo)
      (lo + l.size, ⟨lo, lo + (Tree.node l r).size⟩) (label r (lo + l.size + 1))

/-- A rotation updates only the promoted and demoted node fields, using keys
and bounds already at those two adjacent nodes. Context fields stay untouched. -/
inductive Update : LabelledTree (Nat × Bounds) → LabelledTree (Nat × Bounds) → Prop where
  | right (a b c : LabelledTree (Nat × Bounds)) (x y : Nat) (bx byBounds : Bounds) :
      Update (.node (.node a (x, bx) b) (y, byBounds) c)
        (.node a (x, ⟨bx.low, byBounds.high⟩) (.node b (y, ⟨x + 1, byBounds.high⟩) c))
  | left (a b c : LabelledTree (Nat × Bounds)) (x y : Nat) (bx byBounds : Bounds) :
      Update (.node a (x, bx) (.node b (y, byBounds) c))
        (.node (.node a (x, ⟨bx.low, y⟩) b) (y, ⟨bx.low, byBounds.high⟩) c)
  | inLeft {a b c : LabelledTree (Nat × Bounds)} {entry : Nat × Bounds} :
      Update a b → Update (.node a entry c) (.node b entry c)
  | inRight {a b c : LabelledTree (Nat × Bounds)} {entry : Nat × Bounds} :
      Update a b → Update (.node c entry a) (.node c entry b)

end RotationBST.IntervalMetadata
