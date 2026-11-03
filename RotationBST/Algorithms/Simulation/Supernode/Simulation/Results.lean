module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Simulation.Initial

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode.Simulation.Results

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

end RotationBST.Geometric.Online.Supernode.Simulation.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.Supernode.Simulation.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.Supernode.Simulation.Results allowing [
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
  RotationBST.Algorithms.Simulation.Supernode.Extraction.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Rebuild.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Accounting.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Transition.Defs,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Simulation.Defs]
