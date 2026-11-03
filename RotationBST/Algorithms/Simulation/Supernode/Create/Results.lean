module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Create.Proofs
public import RotationBST.Models.Region.View.Defs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode.Create.Results
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

end RotationBST.Geometric.Online.Supernode.Create.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.Supernode.Create.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.Supernode.Create.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs,
  RotationBST.Structures.SplitTree.Accounting.Abstract,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Defs,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Structures.Treap.Abstract,
  RotationBST.Models.Region.Abstract,
  RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Layer.Defs, RotationBST.Models.Region.View.Defs, RotationBST.Models.Region.Defs]
