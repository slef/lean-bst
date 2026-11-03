module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Exposed split key, with the two remaining intervals both in maximum-finger
representation. -/
def maximumSplitView (cut : Partition.Cut) : Tree :=
  .node (maximumView cut.left.tree).tree (maximumView cut.right.tree).tree

/-- Convert the local interval, split it, and restore both output finger views.
The count includes all three conversions and the balanced splitting rotations. -/
def maximumSplit (height : Nat) (t : Multiway) (rank : Nat) : Partition.Cut :=
  let cut := Partition.run height t rank
  { cut with cost := maximumCost t + cut.cost +
      maximumCost cut.left.tree + maximumCost cut.right.tree }

/-- Rotation count for splitting an interval after an enclosing separator. -/
def maximumSplitOpenCost (height : Nat) (t : Multiway) (rank : Nat) : Nat :=
  let cut := Partition.run height t rank
  maximumOpenCost t + cut.cost + 1 +
    maximumOpenCost cut.left.tree + maximumCost cut.right.tree

end RotationBST.Arboral.Split.Multiway.Finger
