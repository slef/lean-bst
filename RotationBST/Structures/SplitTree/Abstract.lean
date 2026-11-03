module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.AbstractBridge

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
