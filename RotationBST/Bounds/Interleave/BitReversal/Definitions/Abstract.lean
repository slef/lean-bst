module

public import RotationBST.Bounds.Interleave.Definitions.Abstract

@[expose] public section
namespace RotationBST.Wilber.BitReversal

/-- A perfect reference BST with `2^height` leaves. Internal keys separate the
leaves; requests below visit only leaves. -/
def reference : Nat → Tree
  | 0 => .node .nil .nil
  | height + 1 => .node (reference height) (reference height)

/-- Bit-reversal order on the leaves: alternate the two child copies of each
smaller request. Values are full-tree inorder ranks, not leaf indices. -/
def requests : Nat → List Nat
  | 0 => [0]
  | height + 1 => (requests height).flatMap fun x => [x, x + (reference height).size + 1]

end RotationBST.Wilber.BitReversal
