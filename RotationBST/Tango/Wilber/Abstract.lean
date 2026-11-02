module

public import RotationBST.Tango.Definitions.Abstract
public import RotationBST.Tango.Transition.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- Region observations in absolute (rather than subtree-local) ranks. -/
def labels (low cut high : Nat) (xs : List Nat) : List Bool :=
  (xs.filter fun x => low ≤ x ∧ x < high).map (· ≤ cut)

/-- The interleave quantity written in absolute ranks. -/
def absoluteInterleave : Tree → Nat → List Nat → Nat
  | .nil, _, _ => 0
  | .node l r, lo, xs => alternations (labels lo (lo + l.size) (lo + l.size + 1 + r.size) xs) +
      absoluteInterleave l lo xs + absoluteInterleave r (lo + l.size + 1) xs

end RotationBST.Tango
