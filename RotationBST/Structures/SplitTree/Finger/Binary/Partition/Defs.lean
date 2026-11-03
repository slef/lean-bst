module

public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Exposed split key, with the two remaining intervals both in minimum-finger
representation. -/
def splitView (cut : Partition.Cut) : Tree :=
  .node (binaryView cut.left.tree).tree (binaryView cut.right.tree).tree

/-- Convert the local interval, split it, and restore both output finger views.
The count includes all three conversions and the balanced splitting rotations. -/
def fingerSplit (height : Nat) (t : Multiway) (rank : Nat) : Partition.Cut :=
  let cut := Partition.run height t rank
  { cut with cost := conversionCost t + cut.cost +
      conversionCost cut.left.tree + conversionCost cut.right.tree }

/-- Rotation count for splitting an interval before an enclosing separator. -/
def fingerSplitOpenCost (height : Nat) (t : Multiway) (rank : Nat) : Nat :=
  let cut := Partition.run height t rank
  openConversionCost t + cut.cost + 1 +
    conversionCost cut.left.tree + openConversionCost cut.right.tree

end RotationBST.Arboral.Split.Multiway.Finger
