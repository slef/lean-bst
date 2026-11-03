module

public import RotationBST.Models.Region.View.Abstract
public import RotationBST.Models.Region.View.Defs

@[expose] public section
namespace RotationBST.Geometric

/-- A previously touched boundary dominates every key between it and `key`.
These are the neighboring parent keys in the last-touch treap. -/
def LastTouchBoundary (P : Finset Point) (boundary key : Nat) : Prop :=
  boundary ≠ key ∧ ⊥ < lastTouch P boundary ∧
    ∀ y, min boundary key ≤ y → y ≤ max boundary key → y ≠ boundary →
      lastTouch P y < lastTouch P boundary

end RotationBST.Geometric
