module

import RotationBST.Audit.Check
public import RotationBST.Classical.Random.AbstractBridge

@[expose] public section

/-! Random search trees. A treap on the keys `0, …, n - 1` is any tree with the
heap property for a priority order (`Geometric.Heap`, `Structures/Treap/Abstract`);
`average` (`Structures/Treap/Random/Definitions/Abstract`) is the expectation
over a random order, here with uniform weights, so that every order of the `n`
keys is equally likely. (Inserting the keys in that order without rebalancing
builds the same tree; that is ROADMAP entry 9(b) and is not proved here.) -/
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

end RotationBST.Classical.Random.Results

/-- info: abstract audit passed for `RotationBST.Classical.Random.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.Random.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Structures.Treap.Abstract,
  RotationBST.Structures.Treap.Random.Definitions.Abstract]
