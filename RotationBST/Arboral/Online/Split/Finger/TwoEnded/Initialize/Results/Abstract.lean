module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Initialize.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Initialize.Results

/-- Create a valid shared interval of any size, from any BST shape, with a
linear charge covering both initialization and its future splitting budget. -/
theorem create (shape : Tree) :
    IntervalValid (initialInterval shape.size) ∧
      (intervalTree (initialInterval shape.size)).size = shape.size ∧
      ∃ cost, Rotations shape (intervalTree (initialInterval shape.size)) cost ∧
        cost + intervalCredit (initialInterval shape.size) ≤ 6016 * shape.size :=
  ⟨initialInterval_valid _, initialInterval_size _, initialInterval_budget shape⟩

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Initialize.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Initialize.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Abstract,
  RotationBST.Arboral.Online.Split.Accounting.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Partial.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Lifetime.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Initialize.Abstract]
