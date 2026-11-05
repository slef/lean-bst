module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized.Results
open Reference

/-- Lemma 3.19 with explicit charges for previously unseen columns. -/
theorem step (t : Tree) (lo : Nat) (prior : List Nat) (old next : Nat)
    (valid : ∀ x ∈ (prior ++ [old]) ++ [next], lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.keys (prior ++ [old]) next).card + potential t lo ((prior ++ [old]) ++ [next]) ≤
      potential t lo (prior ++ [old]) + 24 * Transitions.edges t lo old next + 24 +
        3 * (unseenKeys (Virgin.points (prior ++ [old])) (Virgin.keys (prior ++ [old]) next)).card :=
  Amortized.step t lo prior old next valid

/-- The exact whole-stream accounting retains final potential and charges
only distinct encountered columns, with startup paid once. -/
theorem stream (t : Tree) (lo : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t) :
    (Virgin.points xs).card + potential t lo xs ≤
      12 * leaves t + 24 * referenceCost t lo xs + 3 * ((Virgin.points xs).image Prod.fst).card :=
  Amortized.stream t lo xs valid

/-- Theorem 3.1 for the actual geometric sweep: twenty-four times the
node-counted leaf-reference benchmark, plus fifteen per reference leaf. -/
theorem cost (t : Tree) (lo : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, lo ≤ x ∧ x < lo + leaves t) :
    rowCost greedySweep 0 ∅ xs ≤ 24 * referenceCost t lo xs + 15 * leaves t :=
  Amortized.cost t lo xs valid

/-- One BST policy works simultaneously for all leaf-oriented references.
Its normalized cost includes requests, rotations, and initialization. -/
theorem bst (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ reference : Tree, leaves reference = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost initial xs ≤
          144456 * referenceCost reference 0 xs + 96303 * n :=
  Amortized.bst n

/-- Actual pointer execution with the same quantifier order and a single
linear initialization allowance. The simulation constants are not sharp. -/
theorem pointer (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ reference : Tree, leaves reference = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution initial xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ∧
        (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ≤
          4622232 * referenceCost reference 0 xs + 3081471 * n :=
  Amortized.pointer n

end RotationBST.Geometric.GreedyASS.Potential.Amortized.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.Amortized.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.Amortized.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Algorithm.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Transitions.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Amortized.Definitions.Abstract]
