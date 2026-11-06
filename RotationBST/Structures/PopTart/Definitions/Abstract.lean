module

public import RotationBST.Models.Pointer.Lazy.Skeleton.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section
namespace RotationBST.PopTart

/-- A pop-tart's active nodes and weighted fringe occurrences. A fringe slot
can hold an entire frozen subtree. Equal-shaped slots may have different
weights, and the outer structure does not inspect their contents. -/
inductive WeightedTree where
  | leaf (subtree : Tree) (weight : ℝ)
  | node (left right : WeightedTree)

namespace WeightedTree

def skeleton : WeightedTree → Pointer.Lazy.Skeleton
  | .leaf t _ => .hole t
  | .node l r => .node l.skeleton r.skeleton

def tree (t : WeightedTree) : Tree := t.skeleton.tree

/-- Total weight of fringe slots; active separator nodes are not included. -/
def mass : WeightedTree → ℝ
  | .leaf _ w => w
  | .node l r => l.mass + r.mass

def Nonnegative : WeightedTree → Prop
  | .leaf _ w => 0 ≤ w
  | .node l r => l.Nonnegative ∧ r.Nonnegative

/-- Number of outer fringe slots, independent of their contents and weights. -/
def leafCount : WeightedTree → Nat
  | .leaf _ _ => 1
  | .node l r => leafCount l + leafCount r

/-- Inorder weighted fringe, retaining distinct weights on equal-shaped slots. -/
def fringe : WeightedTree → List (Tree × ℝ)
  | .leaf t w => [(t, w)]
  | .node l r => l.fringe ++ r.fringe

/-- Nonnegative fringe weights in nonincreasing inorder order. Equal weights
are allowed; the order concerns occurrences, including the bottom leaf. -/
def Ordered (t : WeightedTree) : Prop :=
  t.Nonnegative ∧ t.fringe.Pairwise (fun a b => b.2 ≤ a.2)

/-- A complete crumb of a given height, with arbitrary weighted fringe slots. -/
inductive Perfect : Nat → WeightedTree → Prop where
  | leaf (t : Tree) (w : ℝ) : Perfect 0 (.leaf t w)
  | node {level : Nat} {l r : WeightedTree} :
      Perfect level l → Perfect level r → Perfect (level + 1) (.node l r)

/-- Outer height treats each frozen fringe as one external leaf. -/
def height : WeightedTree → Nat
  | .leaf _ _ => 0
  | .node l r => max l.height r.height + 1

/-- In an ordinary pop-tart every fringe is an empty external leaf. -/
def EmptyFringe : WeightedTree → Prop
  | .leaf t _ => t = .nil
  | .node l r => l.EmptyFringe ∧ r.EmptyFringe

/-- A particular weighted fringe occurrence at a given outer depth. The
relation retains its weight even if the same subtree occurs elsewhere. -/
inductive SlotAt : WeightedTree → Tree → ℝ → Nat → Prop where
  | leaf (t : Tree) (w : ℝ) : SlotAt (.leaf t w) t w 0
  | left {l r : WeightedTree} {t : Tree} {w : ℝ} {depth : Nat} :
      SlotAt l t w depth → SlotAt (.node l r) t w (depth + 1)
  | right {l r : WeightedTree} {t : Tree} {w : ℝ} {depth : Nat} :
      SlotAt r t w depth → SlotAt (.node l r) t w (depth + 1)

end WeightedTree
end RotationBST.PopTart
