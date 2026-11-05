module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.OptimalLazyFinger.Work.AbstractBridge

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work.Results

/-- Erasing the annotations yields exactly the existing executable optimizer. -/
theorem same_tree (n p : Nat) (xs : List Nat) :
    (treeFrom n p xs).ret = OptimalLazyFinger.treeFrom n p xs := treeFrom_ret n p xs

/-- Transition accumulation and prefix preprocessing cost linearly in the
request count and quadratically in the stored universe size. -/
theorem preprocessing (n p : Nat) (xs : List Nat) :
    (prepare n p xs).time ≤ 4 * xs.length + 14 * n ^ 2 + 18 * n + 7 := prepare_time n p xs

/-- Exact optimality and an end-to-end cubic work bound, in the cost model of
`Work.Model.Abstract`. This includes root initialization and empty instances. -/
theorem root_start (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (tree n xs).ret.size = n ∧
      LazyFinger.cost (tree n xs).ret xs = LazyFinger.optimalCost n xs ∧
      (tree n xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := tree_spec n xs valid

/-- The same guarantee with a specified initial key. -/
theorem specified_start (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (treeFrom n p xs).ret.size = n ∧
      LazyFinger.costFrom (treeFrom n p xs).ret p xs = LazyFinger.optimalCostFrom n p xs ∧
      (treeFrom n p xs).time ≤ 4 * xs.length + 64 * (n + 1) ^ 3 := treeFrom_spec n p xs hp valid

/-- The usual `O(m+n³)` form on nonempty universes, as an explicit inequality. -/
theorem nonempty_bound (n p : Nat) (xs : List Nat) (hn : 0 < n) :
    (treeFrom n p xs).time ≤ 4 * xs.length + 512 * n ^ 3 := treeFrom_time_nonempty n p xs hn

end RotationBST.OptimalLazyFinger.Work.Results

/-- info: abstract audit passed for `RotationBST.OptimalLazyFinger.Work.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.OptimalLazyFinger.Work.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Edges.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract,
  RotationBST.Structures.PrefixSum.Definitions.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Definitions.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Work.Model.Abstract,
  RotationBST.Algorithms.OptimalLazyFinger.Work.Definitions.Abstract]
