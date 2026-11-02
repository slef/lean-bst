module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Open

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Partition.Results

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

end RotationBST.Arboral.Split.Multiway.Finger.Partition.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Partition.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract]
