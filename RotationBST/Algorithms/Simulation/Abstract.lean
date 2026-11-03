module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.AbstractBridge

@[expose] public section

/-! The causal geometric-to-BST simulation (Demaine, Harmon, Iacono, Kane, and
Pătraşcu, 2009, made online). The policy is existential: the proof constructs
it from last-touch supernodes represented by shared split trees, and the
statements below mention only the models. The constants are not claimed sharp. -/
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
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Online.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Algorithm.Abstract]
