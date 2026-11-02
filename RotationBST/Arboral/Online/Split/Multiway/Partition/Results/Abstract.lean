module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Multiway.Partition.Cost.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Partition.Results

/-- Split at an arbitrary existing rank by actual BST rotations. Both remaining
intervals retain balanced multiway representations and their exact key counts.
The finger-distance and amortized split bounds are separate obligations. -/
theorem split {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let result := run h t rank
    Access t.binary result.binary rank result.cost ∧ result.Valid ∧
      result.left.tree.size = rank ∧ result.right.tree.size = t.size - rank - 1 :=
  ⟨(run_spec valid rank existsKey).2, (run_spec valid rank existsKey).1,
    run_sizes valid rank existsKey⟩

/-- Root-based splitting preserves the height ceiling and uses at most fourteen
rotations per input level. The smaller-side finger bound is not asserted here. -/
theorem rebuilding {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let result := run h t rank
    result.left.height ≤ h ∧ result.right.height ≤ h ∧ result.cost ≤ 14 * h :=
  ⟨(run_height valid rank existsKey).1, (run_height valid rank existsKey).2,
    run_cost valid rank existsKey⟩

end RotationBST.Arboral.Split.Multiway.Partition.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Partition.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract]
