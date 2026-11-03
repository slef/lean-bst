module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Policy.Total

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Policy.Results

/-- Fix the initial BST and an online geometric algorithm. A single BST
algorithm, chosen before the sequence, simulates every valid request sequence
with constant cost per geometric point and linear initialization cost. -/
theorem online_simulation (tree : Tree) (A : OnlineAlgorithm tree.size) :
    ∃ algorithm : Algorithm, ∀ xs : List Nat, (∀ x ∈ xs, x < tree.size) →
      algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6016 * tree.size :=
  online_policy tree A

/-- A single policy works for all initial trees of the given size and all
valid sequences. The additive initialization term is paid only once. -/
theorem uniform_simulation (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6018 * n :=
  uniform_online_policy n A

/-- Conventional normalized cost includes one charge for every request. -/
theorem normalized_simulation (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost tree xs ≤ 6019 * rowCost A.step 0 ∅ xs + 6018 * n :=
  uniform_online_total n A

/-- The fixed causal pointer strategy serves every request and has linear
cost in the geometric point count, including initialization. -/
theorem pointer_simulation (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution tree xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).2 ∧
        (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).2 ≤
          192593 * rowCost A.step 0 ∅ xs + 192576 * n :=
  uniform_online_pointer n A

end RotationBST.Arboral.Online.Supernode.Policy.Results

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Policy.Results allowing [
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
  RotationBST.Algorithms.Simulation.Supernode.Transition.Defs,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Simulation.Defs,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Algorithm.Abstract]
