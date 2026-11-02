module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Abstract
public import Mathlib.Data.Finset.Basic

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Pull current full-tree touches back to this supernode's key-only ranks. -/
def touchedRanks (count : Nat) (gaps : Nat → Tree) (offset lo : Nat) (keys : Finset Nat) : Finset Nat :=
  (Finset.range count).filter fun rank => lo + keyRank gaps offset rank ∈ keys

end RotationBST.Arboral.Online.Supernode
