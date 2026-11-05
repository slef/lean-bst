module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Performance.AbstractBridge

@[expose] public section
/-! The ordinary lazy-finger and weighted dynamic-finger bounds of
Iacono and Langerman (arXiv:1810.01785, Theorems 4.1–4.2 and Corollary 1).
Costs include a unit per request and an explicit linear startup allowance.
The weight optimum is an infimum; no attainment is assumed. The causal
BST/pointer policies are chosen before the benchmark or request sequence.
The combined guarantees of Theorem 4.3 are separate and remain unfinished. -/
namespace RotationBST.Geometric.GreedyASS.Performance.Results

theorem lazy_from (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.costFrom t p xs + 15 * t.size :=
  Performance.lazy_from t p xs hp valid

theorem lazy_tree (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.cost t xs + 15 * t.size :=
  Performance.lazy_tree t xs valid

theorem lazy_optimal (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.optimalCost n xs + 15 * n :=
  Performance.lazy_optimal n xs valid

theorem lazy_optimal_from (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    rowCost greedySweep 0 ∅ xs ≤ 120 * LazyFinger.optimalCostFrom n p xs + 15 * n :=
  Performance.lazy_optimal_from n p xs hp valid

theorem weighted_optimal (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * WeightedFinger.optimalCostFrom n p xs + 15 * n :=
  Performance.weighted_optimal n p xs hp valid

theorem weighted (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (positive : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * WeightedFinger.costFrom w p xs + 15 * n :=
  Performance.weighted w n p xs positive hp valid

theorem dynamic (n p : Nat) (xs : List Nat) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * Bounds.dynamicFingerCostFrom p xs + 15 * n :=
  Performance.dynamic n p xs hp valid

theorem bst (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost initial xs ≤ 722280 * LazyFinger.optimalCost n xs + 96303 * n ∧
        ∀ p, p < n → (algorithm.totalCost initial xs : ℝ) ≤
          2889120 * WeightedFinger.optimalCostFrom n p xs + 96303 * n :=
  Performance.bst n

theorem pointer (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution initial xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ∧
        (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ≤
          23111160 * LazyFinger.optimalCost n xs + 3081471 * n ∧
        ∀ p, p < n →
          ((Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 : ℝ) ≤
            92444640 * WeightedFinger.optimalCostFrom n p xs + 3081471 * n :=
  Performance.pointer n

theorem bst_weighted (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ w : Nat → ℝ, (∀ k < n, 0 < w k) →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        (algorithm.totalCost initial xs : ℝ) ≤ 2889120 * WeightedFinger.costFrom w p xs + 96303 * n :=
  Performance.bst_weighted n

theorem bst_dynamic (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        (algorithm.totalCost initial xs : ℝ) ≤ 2889120 * Bounds.dynamicFingerCostFrom p xs + 96303 * n :=
  Performance.bst_dynamic n

theorem pointer_weighted (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ w : Nat → ℝ, (∀ k < n, 0 < w k) →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution initial xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ∧
        ((Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 : ℝ) ≤
          92444640 * WeightedFinger.costFrom w p xs + 3081471 * n :=
  Performance.pointer_weighted n

end RotationBST.Geometric.GreedyASS.Performance.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Performance.Results`: 12 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Performance.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Online.Algorithm.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract,
  RotationBST.Bounds.DynamicFinger.Definitions.Abstract]
