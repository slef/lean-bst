module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Transition.Results

/-- Recursive extraction spends existing nested credit and preserves every
unused portion in its retained holes. -/
theorem extraction_credit (keys : Finset Nat) {P : Finset Point}
    {lo : Nat} {state : Nested} (represented : Represents P lo state) :
    (extractRow keys lo state).2 + (extractRow keys lo state).1.credit ≤ state.credit :=
  extract_credit _ keys represented

/-- A legal row produces its next canonical stored state using only the old
state and current keys. Rotation cost plus remaining potential is bounded
by old potential plus a constant per current-row point. -/
theorem transition {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    {state : Nested} (represented : Represents P 0 state) (size : state.tree.size = n) :
    Represents (P ∪ row time keys) 0 (nextState state keys) ∧
      ∃ cost, Rotations state.tree (nextState state keys).tree cost ∧
        cost + (nextState state keys).credit ≤ state.credit + 6016 * keys.card :=
  nextState_spec history legal represented size

end RotationBST.Arboral.Online.Supernode.Transition.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Transition.Results allowing [
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
  RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Rebuild.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Abstract]
