module

import RotationBST.Audit.Check
public import RotationBST.Classical.Random.AbstractBridge

@[expose] public section

/-! Random search trees. A treap on the keys `0, …, n - 1` is any tree with the
heap property for a priority order (`Geometric.Heap`, `Structures/Treap/Abstract`);
`average` (`Structures/Treap/Random/Definitions/Abstract`) is the expectation
over a random order, here with uniform weights, so that every order of the `n`
keys is equally likely. Inserting the keys in that order without rebalancing
(`insertAll`, `Definitions/Abstract`) builds exactly that treap. -/
namespace RotationBST.Classical.Random.Results

/-- **Expected depth in a random treap**: `H(x + 1) + H(n - x) - 2`. -/
theorem expected_depth (n x : Nat) (hx : x < n) (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) 0) :
    Treap.Random.average (fun _ => 1) (Finset.range n) (fun xs => ((T xs).depth x : ℝ)) =
      ((harmonic (x + 1) : ℚ) : ℝ) + ((harmonic (n - x) : ℚ) : ℝ) - 2 :=
  Random.expected_depth n x hx T spec

/-- In particular every expected depth is at most `2 ln n`. -/
theorem expected_depth_le (n x : Nat) (hx : x < n) (T : List Nat → Tree)
    (spec : ∀ xs, (T xs).size = n ∧ Geometric.Heap xs.idxOf (T xs) 0) :
    Treap.Random.average (fun _ => 1) (Finset.range n) (fun xs => ((T xs).depth x : ℝ)) ≤
      2 * Real.log n :=
  Random.expected_depth_le n x hx T spec

/-- **Insertion builds the treap of the insertion order**: inserting a
permutation of the `n` keys without rebalancing gives the tree with the heap
property for the positions in the order. -/
theorem insertAll_treap (n : Nat) (order : List Nat) (h : order.Perm (List.range n)) :
    (insertAll order).erase.size = n ∧ Geometric.Heap order.idxOf (insertAll order).erase 0 :=
  Random.insertAll_treap n order h

/-- **Random binary search trees.** Inserting the keys in a uniformly random
order, key `x` has expected depth `H(x + 1) + H(n - x) - 2`… -/
theorem random_bst_depth (n x : Nat) (hx : x < n) :
    Treap.Random.average (fun _ => 1) (Finset.range n) (fun xs => ((insertAll xs).erase.depth x : ℝ)) =
      ((harmonic (x + 1) : ℚ) : ℝ) + ((harmonic (n - x) : ℚ) : ℝ) - 2 :=
  Random.random_bst_depth n x hx

/-- …at most `2 ln n`. -/
theorem random_bst_depth_le (n x : Nat) (hx : x < n) :
    Treap.Random.average (fun _ => 1) (Finset.range n) (fun xs => ((insertAll xs).erase.depth x : ℝ)) ≤
      2 * Real.log n :=
  Random.random_bst_depth_le n x hx

end RotationBST.Classical.Random.Results

/-- info: abstract audit passed for `RotationBST.Classical.Random.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.Random.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Structures.Treap.Abstract,
  RotationBST.Structures.Treap.Random.Definitions.Abstract,
  RotationBST.Classical.Random.Definitions.Abstract]
