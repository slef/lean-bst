module

public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

/-- Plan a balanced 2–3–4 shape of any requested size by rightmost insertion.
This computes a target shape; its planning work is not a BST rotation trace. -/
def balancedShape : Nat → Multiway.Partition.Piece
  | 0 => ⟨.nil, 0⟩
  | n + 1 =>
      let previous := balancedShape n
      let joined := Multiway.Join.run previous.height 0 previous.tree .nil
      ⟨joined.tree, joined.height⟩

/-- Initial shared representation for a newly created supernode. -/
def initialInterval : Nat → Option State
  | 0 => none
  | n + 1 => some (fromRoot (balancedShape (n + 1)).height (balancedShape (n + 1)).tree).1

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
