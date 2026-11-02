module

public import RotationBST.Arboral.Definitions.Abstract
public import RotationBST.Model.Abstract

@[expose] public section
namespace RotationBST.Arboral

/-- In each row, the touched keys form a rooted connected region of one fixed
BST. The root has absolute rank `lo + left.size`; subtrees stay unlabelled. -/
def RootedRows : Tree → Nat → Finset Point → Prop
  | .nil, _, P => P = ∅
  | .node l r, lo, P =>
      (∀ p ∈ P, (lo + l.size, p.2) ∈ P) ∧
      RootedRows l lo (P.filter fun p => p.1 < lo + l.size) ∧
      RootedRows r (lo + l.size + 1) (P.filter fun p => lo + l.size < p.1)

end RotationBST.Arboral
