module

public import RotationBST.Bounds.LazyFinger.Definitions.Abstract
public import Mathlib.Data.Finset.Range

@[expose] public section
namespace RotationBST.LazyFinger

/-- Existing ranks at lazy-finger distance at most `radius` from `x`. -/
def ball (t : Tree) (x radius : Nat) : Finset Nat :=
  (Finset.range t.size).filter fun y => distance t x y ≤ radius

end RotationBST.LazyFinger
