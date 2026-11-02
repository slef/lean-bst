module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Rebuild.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Rebuild.Results

/-- Rebuild an extracted region into the canonical state for its new row,
retaining every nested child. Rebuilding and the new supernode's future
splitting credit cost at most a constant per exposed key. -/
theorem rebuilding {n time : Nat} {P : Finset Point}
    (history : History n time P) {assembly : Assembly} {lo : Nat}
    (valid : assembly.Valid P lo) :
    Represents (P ∪ row time (Region.keys assembly.region lo)) lo assembly.rebuild ∧
      ∃ cost, Rotations assembly.region.tree assembly.rebuild.tree cost ∧
        cost + Split.Multiway.Finger.TwoEnded.intervalCredit
          (Split.Multiway.Finger.TwoEnded.initialInterval assembly.shape.size) ≤
          6016 * (Region.keys assembly.region lo).card :=
  Assembly.rebuild_spec history valid

end RotationBST.Arboral.Online.Supernode.Rebuild.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Rebuild.Results allowing [
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
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Initialize.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Arboral.Definitions.Abstract,
  RotationBST.Arboral.Treap.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract,
  RotationBST.Arboral.View.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Layer.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Nested.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Ranks.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Select.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Assembly.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Rebuild.Abstract]
