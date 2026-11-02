module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Policy.Total

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
  RotationBST.Arboral.Online.LastTouch.Supernode.Simulation.Abstract,
  RotationBST.Online.Abstract,
  RotationBST.Pointer.Machine.Abstract,
  RotationBST.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Online.Algorithm.Abstract]
