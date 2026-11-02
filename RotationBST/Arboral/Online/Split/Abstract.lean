module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Accounting.Proofs
public import RotationBST.Arboral.Online.Split.Multiway.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Edges.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Context.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Extract.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Join.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Results.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Partition.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Locate.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Select.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Initialize.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Join.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Repair.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Partition.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Results.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Binary.Extract.Amortized.Results.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Results

/-- Smaller-side logarithmic charges sum to at most twice the number of keys,
for every complete split hierarchy. This is the accounting lemma; a BST split
implementation and its per-operation bound are separate obligations. -/
theorem linear_accounting (hierarchy : Tree) : totalCharge hierarchy ≤ 2 * hierarchy.size :=
  totalCharge_linear hierarchy

end RotationBST.Arboral.Split.Results

#check_bst_abstract RotationBST.Arboral.Split.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Accounting.Abstract]
