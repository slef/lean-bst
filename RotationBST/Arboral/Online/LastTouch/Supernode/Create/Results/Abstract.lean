module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Create.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Create.Results
open Split.Multiway.Finger.TwoEnded

/-- Promote the current active keys into a new initialized supernode. Creation
and its whole lifetime splitting budget are charged to these keys once. -/
theorem create {n time : Nat} {P : Finset Point} (history : History n time P)
    (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat)
    (gapHeaps : ∀ hole ∈ Region.holes (withGaps shape gaps offset) lo,
      Heap (fun key => OrderDual.toDual (lastTouch P key)) hole.2 hole.1) :
    let input := initialInterval shape.size
    let source := withGaps shape gaps offset
    let target := withGaps (intervalTree input) gaps offset
    IntervalValid input ∧ ∃ cost,
      Rotations source.tree target.tree cost ∧ Region.Same source target lo ∧
      Layer (P ∪ row time (Region.keys source lo)) (time : WithBot Nat) target lo ∧
      cost + intervalCredit input ≤ 6016 * (Region.keys source lo).card :=
  create_supernode history shape gaps offset lo gapHeaps

end RotationBST.Arboral.Online.Supernode.Create.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Create.Results allowing [
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
  RotationBST.Arboral.Online.LastTouch.Supernode.Layer.Abstract]
