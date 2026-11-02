module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Rebuild.Abstract

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Unspent splitting credit over all stored supernodes. -/
def Nested.credit : Nested → Nat
  | .empty => 0
  | .layer state children => intervalCredit (some state) + (children.map Nested.credit).sum

/-- Exposed keys carry no old credit; retained nested holes keep theirs. -/
def Assembly.credit : Assembly → Nat
  | .hole state => state.credit
  | .node left right => left.credit + right.credit

end RotationBST.Arboral.Online.Supernode
