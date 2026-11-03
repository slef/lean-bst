module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Partition.Open

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.Partition.Results

/-- Split a finger BST and retain balanced minimum-finger views on both sides.
The bound depends on the input interval's height, not yet the nearer endpoint. -/
theorem split {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let result := fingerSplit h t rank
    Access (binaryView t).tree (splitView result) rank result.cost ∧
      result.Valid ∧ result.cost ≤ 23 * h ∧
      result.left.height ≤ h ∧ result.right.height ≤ h :=
  ⟨fingerSplit_access valid rank existsKey, (Multiway.Partition.run_spec valid rank existsKey).1,
    fingerSplit_cost valid rank existsKey, Multiway.Partition.run_height valid rank existsKey⟩

/-- A local interval can be split without modifying its enclosing remainder. -/
theorem before_remainder {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) (rest : Tree) :
    let cut := Multiway.Partition.run h t rank
    Access (openView t rest) (.node (binaryView cut.left.tree).tree (openView cut.right.tree rest))
      rank (fingerSplitOpenCost h t rank) ∧ fingerSplitOpenCost h t rank ≤ 23 * h + 1 :=
  ⟨fingerSplit_open_access valid rank existsKey rest, fingerSplit_open_cost valid rank existsKey⟩

end RotationBST.SplitTree.Multiway.Finger.Partition.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Finger.Partition.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Finger.Partition.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs]
