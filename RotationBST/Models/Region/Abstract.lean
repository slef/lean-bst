module

public import RotationBST.Models.Geometric.Definitions.Abstract
public import RotationBST.Models.Pointer.Lazy.Skeleton.Abstract

@[expose] public section
namespace RotationBST

/-- A rooted region of a BST: the active nodes near the root, with untouched
subtrees hanging from its holes. -/
abbrev Region := Pointer.Lazy.Skeleton

namespace Region

/-- Absolute inorder ranks of the nodes which may be rearranged. -/
def keys : Region → Nat → Finset Nat
  | .hole _, _ => ∅
  | .node l r, lo => insert (lo + l.tree.size)
      (keys l lo ∪ keys r (lo + l.tree.size + 1))

/-- Untouched fringe subtrees, with their absolute inorder offsets. -/
def holes : Region → Nat → List (Nat × Tree)
  | .hole t, lo => [(lo, t)]
  | .node l r, lo => holes l lo ++ holes r (lo + l.tree.size + 1)

/-- Reordering preserves all active keys and the exact untouched fringe. -/
def Same (s t : Region) (lo : Nat) : Prop :=
  s.tree.size = t.tree.size ∧ keys s lo = keys t lo ∧ holes s lo = holes t lo

end Region
end RotationBST
