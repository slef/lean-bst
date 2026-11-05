module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Random.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Random.Results
open Treap.Random

/-- Exact expected distance for one family of weighted random treaps, uniformly
for all valid pairs. The logarithmic consequence is stated below. -/
theorem expected_distance (w : Nat → ℝ) (n lo : Nat)
    (hw : ∀ k ∈ Finset.Ico lo (lo + n), 0 < w k) :
    ∃ T : List Nat → Tree, (∀ xs, (T xs).size = n) ∧
      ∀ x y, lo ≤ x → x < lo + n → lo ≤ y → y < lo + n →
        average w (Finset.Ico lo (lo + n)) (fun xs => (distance (T xs) (x - lo) (y - lo) : ℝ)) =
        ∑ a ∈ Finset.Ico lo (lo + n),
          (w a / (∑ k ∈ Finset.Icc (min a x) (max a x), w k) +
           w a / (∑ k ∈ Finset.Icc (min a y) (max a y), w k) -
           2 * (w a / (∑ k ∈ Finset.Icc (min a (min x y)) (max a (max x y)), w k))) := exists_expected_distance w n lo hw

/-- The same random family satisfies the weighted dynamic-finger bound for
all pairs. This counts one request plus movement and uses base-two logarithms. -/
theorem weighted_charge (w : Nat → ℝ) (n : Nat) (hw : ∀ k < n, 0 < w k) :
    ∃ T : List Nat → Tree, (∀ xs, (T xs).size = n) ∧
      ∀ x y, x < n → y < n →
        average w (Finset.range n) (fun xs => 1 + (distance (T xs) x y : ℝ)) ≤
          4 * WeightedFinger.charge w x y := exists_expected_charge_bound w n hw

end RotationBST.LazyFinger.Random.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Random.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Random.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Structures.Treap.Random.Definitions.Abstract,
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract]
