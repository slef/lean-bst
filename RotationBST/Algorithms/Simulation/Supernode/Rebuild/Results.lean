module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Rebuild.Proofs

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

/-- info: abstract audit passed for `RotationBST.Arboral.Online.Supernode.Rebuild.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Online.Supernode.Rebuild.Results allowing [
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
  RotationBST.Algorithms.Simulation.Supernode.Layer.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Nested.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Ranks.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Select.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Assembly.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Rebuild.Defs]
