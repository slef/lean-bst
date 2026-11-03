module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section
namespace RotationBST.Wilber

/-- The shallowest node in the half-open key interval `[low, high)`, in a tree
whose inorder interval starts at `lo`. Empty intervals return `none`. -/
def topIn : Tree → Nat → Nat → Nat → Option Nat
  | .nil, _, _, _ => none
  | .node l r, lo, low, high =>
      if lo + l.size < low then topIn r (lo + l.size + 1) low high
      else if high ≤ lo + l.size then topIn l lo low high
      else some (lo + l.size)

/-- The transition point of a nontrivial reference cut: the shallowest key
on the side opposite the shallowest key of the whole interval. -/
def transition (t : Tree) (low cut high : Nat) : Option Nat :=
  match topIn t 0 low high with
  | none => none
  | some root => if root ≤ cut then topIn t 0 (cut + 1) high else topIn t 0 low (cut + 1)

/-- Transition keys of all reference cuts. Empty right regions contribute none. -/
def transitionKeys : Tree → Nat → Tree → List Nat
  | .nil, _, _ => []
  | .node l r, lo, actual =>
      (transition actual lo (lo + l.size) (lo + l.size + 1 + r.size)).toList ++
      transitionKeys l lo actual ++ transitionKeys r (lo + l.size + 1) actual

end RotationBST.Wilber
