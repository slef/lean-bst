module

public import RotationBST.Bounds.Interleave.Definitions.Abstract

@[expose] public section
namespace RotationBST.Wilber

/-- Region observations in absolute (rather than subtree-local) ranks. -/
def labels (low cut high : Nat) (xs : List Nat) : List Bool :=
  (xs.filter fun x => low ≤ x ∧ x < high).map (· ≤ cut)

end RotationBST.Wilber
