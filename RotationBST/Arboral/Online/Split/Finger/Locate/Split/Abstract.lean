module

public import RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Expose a rank by splitting its small containing interval. The enclosing
remainder is retained; rebalancing that context is a subsequent operation. -/
def splitLocated (t : Multiway) (rank : Nat) : Tree × Nat :=
  let location := locate t rank
  match contextRemainder location.outer with
  | none =>
      let cut := fingerSplit location.height location.focus rank
      (splitView cut, cut.cost)
  | some rest =>
      let cut := Multiway.Partition.run location.height location.focus rank
      (.node (binaryView cut.left.tree).tree (openView cut.right.tree rest),
        fingerSplitOpenCost location.height location.focus rank)

end RotationBST.Arboral.Split.Multiway.Finger
