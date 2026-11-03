module

public import RotationBST.Bounds.Interleave.Wilber.Abstract
public import RotationBST.Bounds.Interleave.Transition.Defs

/-! Internal definitions of the interleave lower-bound proof. -/

@[expose] public section
namespace RotationBST.Wilber

/-- The interleave quantity written in absolute ranks. -/
def absoluteInterleave : Tree → Nat → List Nat → Nat
  | .nil, _, _ => 0
  | .node l r, lo, xs => alternations (labels lo (lo + l.size) (lo + l.size + 1 + r.size) xs) +
      absoluteInterleave l lo xs + absoluteInterleave r (lo + l.size + 1) xs

end RotationBST.Wilber
