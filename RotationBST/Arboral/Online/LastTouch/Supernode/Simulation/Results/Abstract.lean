module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Simulation.Initial

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Simulation.Results

/-- Serve the request at the root and pay for restoring the canonical state.
The potential bound includes both parts of the execution. -/
theorem row_access {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    {state : Nested} (represented : Represents P 0 state) (size : state.tree.size = n) :
    Represents (P ∪ row time keys) 0 (nextState state keys) ∧
      ∃ served accessCost restoreCost,
        Access state.tree served request accessCost ∧
        Rotations served (nextState state keys).tree restoreCost ∧
        accessCost + restoreCost + (nextState state keys).credit ≤ state.credit + 6018 * keys.card :=
  nextState_access history legal represented size

/-- Any geometric run admits a root-access execution whose total rotations
are linear in its row-point count, with a linear initialization term. -/
theorem execution (tree : Tree) (A : OnlineAlgorithm tree.size) (xs : List Nat)
    (bounds : ∀ x ∈ xs, x < tree.size) :
    ∃ target cost, Execution tree xs target cost ∧
      cost ≤ 6018 * rowCost A.step 0 ∅ xs + 6016 * tree.size :=
  geometric_execution tree A xs bounds

end RotationBST.Arboral.Online.Supernode.Simulation.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Simulation.Results allowing [
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
  RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Abstract,
  RotationBST.Arboral.Online.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Simulation.Abstract]
