module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Results

/-- Split a balanced maximum-finger interval, preserving both output views. -/
theorem split {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (maximumView t).tree (maximumSplitView (maximumSplit h t rank))
      rank (maximumSplit h t rank).cost ∧ (maximumSplit h t rank).cost ≤ 23 * h :=
  ⟨maximumSplit_access valid rank existsKey, maximumSplit_cost valid rank existsKey⟩

/-- An enclosing smaller-key remainder is retained, with one extra rotation. -/
theorem split_open {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) (rest : Tree) :
    let cut := Multiway.Partition.run h t rank
    Access (maximumOpenView t rest)
      (.node (maximumOpenView cut.left.tree rest) (maximumView cut.right.tree).tree)
      (rest.size + 1 + rank) (maximumSplitOpenCost h t rank) ∧
      maximumSplitOpenCost h t rank ≤ 23 * h + 1 :=
  ⟨maximumSplit_open_access valid rank existsKey rest, maximumSplit_open_cost valid rank existsKey⟩

/-- A last-child interval and its remainder describe the original finger tree. -/
theorem context (fs : List Context.Frame) (focus : Multiway)
    (right : ∀ f ∈ fs, IsRightFrame f) :
    (maximumView (Context.plug fs focus)).tree = maximumEnclosingView focus fs :=
  maximumEnclosingView_eq fs focus right

end RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.Maximum.Partition.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs]
