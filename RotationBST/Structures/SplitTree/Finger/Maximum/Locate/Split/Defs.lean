module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

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

end RotationBST.Geometric.Split.Multiway.Finger
