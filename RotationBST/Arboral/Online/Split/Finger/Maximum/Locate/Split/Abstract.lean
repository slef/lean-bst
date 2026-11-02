module

public import RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Expose the key at the given distance from the maximum, splitting only its
containing interval and retaining the smaller-key enclosing remainder. -/
def splitLocatedMaximum (t : Multiway) (distance : Nat) : Tree × Nat :=
  let location := locateMaximum t distance
  let rank := location.focus.size - 1 - distance
  match maximumContextRemainder location.outer with
  | none =>
      let cut := maximumSplit location.height location.focus rank
      (maximumSplitView cut, cut.cost)
  | some rest =>
      let cut := Multiway.Partition.run location.height location.focus rank
      (.node (maximumOpenView cut.left.tree rest) (maximumView cut.right.tree).tree,
        maximumSplitOpenCost location.height location.focus rank)

end RotationBST.Arboral.Split.Multiway.Finger
