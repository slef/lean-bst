module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Transition.Proofs

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
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Context.Defs,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Defs,
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
  RotationBST.Structures.SplitTree.Accounting.Defs,
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
  RotationBST.Algorithms.Simulation.Supernode.Extraction.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Rebuild.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Accounting.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Transition.Defs]
