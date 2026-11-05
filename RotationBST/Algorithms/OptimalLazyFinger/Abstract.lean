module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.OptimalLazyFinger.AbstractBridge

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Results

/-- The table stores exactly the recursively specified solution for each valid
interval, including the minimizing shape and deterministic tie breaking. -/
theorem cached_recurrence (w : Nat → Nat → Nat) (univSize stages n lo : Nat)
    (hn : n ≤ stages) (valid : lo + n ≤ univSize) :
    lookup (tabulate w univSize stages) n lo = solve w n lo :=
  tabulate_lookup w univSize stages n lo hn valid

/-- Optimizing arbitrary interval tolls returns a shape of the requested size,
its exact cost, and a cost no greater than that of any competing shape. -/
theorem boundary_optimal (w : Nat → Nat → Nat) (n : Nat) :
    (optimize w n).1.size = n ∧
      LazyFinger.intervalCost w (optimize w n).1 0 = (optimize w n).2 ∧
      ∀ t : Tree, t.size = n → (optimize w n).2 ≤ LazyFinger.intervalCost w t 0 :=
  optimize_spec w n

/-- The one-pass array accumulator stores the directed adjacent-pair counts. -/
theorem pair_frequencies (n p : Nat) (xs : List Nat) (i j : Nat) (hi : i < n) (hj : j < n) :
    PrefixSum.get (Preprocessing.frequencies n p xs) i j = LazyFinger.frequency p xs i j :=
  Preprocessing.get_frequencies n p xs i j hi hj

/-- Four prefix-sum rectangle queries return the exact sequence boundary toll. -/
theorem prepared_boundary (n p : Nat) (xs : List Nat) (hp : p < n)
    (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    Preprocessing.toll (Preprocessing.prepare n p xs) n lo hi = LazyFinger.crossings lo hi p xs :=
  Preprocessing.toll_prepare n p xs hp valid lo hi hlo hhi

/-- A constructive optimizer for lazy finger with a specified initial key. -/
theorem specified_start (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (treeFrom n p xs).size = n ∧
      LazyFinger.costFrom (treeFrom n p xs) p xs = LazyFinger.optimalCostFrom n p xs :=
  ⟨treeFrom_size n p xs, treeFrom_optimal n p xs hp valid⟩

/-- A constructive optimizer for the root-start benchmark, including the empty
universe and exact initialization cost. No asymptotic cost term is discarded. -/
theorem root_start (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (tree n xs).size = n ∧ LazyFinger.cost (tree n xs) xs = LazyFinger.optimalCost n xs :=
  ⟨tree_size n xs, tree_optimal n xs valid⟩

end RotationBST.OptimalLazyFinger.Results

/-- info: abstract audit passed for `RotationBST.OptimalLazyFinger.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.OptimalLazyFinger.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract,
  RotationBST.Structures.PrefixSum.Definitions.Abstract]
