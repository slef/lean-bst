module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Accounting.Proofs
public import RotationBST.Structures.SplitTree.Multiway.Results
public import RotationBST.Structures.SplitTree.Multiway.Edges.Results
public import RotationBST.Structures.SplitTree.Multiway.Context.Results
public import RotationBST.Structures.SplitTree.Multiway.Extract.Results
public import RotationBST.Structures.SplitTree.Multiway.Join.Results
public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Results
public import RotationBST.Structures.SplitTree.Multiway.Partition.Results
public import RotationBST.Structures.SplitTree.Finger.Results
public import RotationBST.Structures.SplitTree.Finger.Locate.Results
public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Results
public import RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Select.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Results
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Partition.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Join.Results
public import RotationBST.Structures.SplitTree.Finger.Repair.Results
public import RotationBST.Structures.SplitTree.Finger.Partition.Results
public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Results
public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Amortized.Results

@[expose] public section
namespace RotationBST.Arboral.Split.Results

/-- Smaller-side logarithmic charges sum to at most twice the number of keys,
for every complete split hierarchy. This is the accounting lemma; a BST split
implementation and its per-operation bound are separate obligations. -/
theorem linear_accounting (hierarchy : Tree) : totalCharge hierarchy ≤ 2 * hierarchy.size :=
  totalCharge_linear hierarchy

end RotationBST.Arboral.Split.Results

#check_bst_abstract RotationBST.Arboral.Split.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Accounting.Defs]
