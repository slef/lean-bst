module

public import RotationBST.Structures.FingerHand.Packed.Updates.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Make a specified reference key available as a pseudofinger while retaining
all existing pseudofingers. At most one new hand vertex is introduced. -/
structure Exposure (before after : Hand) (key : Nat) : Prop where
  valid : after.Valid
  reference : after.reference = before.reference
  keys : ∀ lo, (before.labels lo).inorder.Sublist (after.labels lo).inorder
  count : after.count ≤ before.count + 1
  retained : key ∈ (after.labels 0).inorder

end RotationBST.FingerHand.Hand
