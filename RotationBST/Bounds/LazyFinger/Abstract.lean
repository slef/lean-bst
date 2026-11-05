module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Results

/-- The fixed-tree lazy-finger benchmark is no worse than twice root finger.
This is the elementary comparison in §1.4 of arXiv:1304.6897, with request
charges included and the initial finger at the root. -/
theorem root_finger (t : Tree) (xs : List Nat) :
    cost t xs ≤ 2 * StaticTree.cost t xs := cost_le_twice_static t xs

theorem symmetric (t : Tree) (x y : Nat) : distance t x y = distance t y x :=
  distance_symm t x y

theorem repeated_key (t : Tree) (x : Nat) (hx : x < t.size) :
    distance t x x = 0 := distance_self t x hx

theorem request_charge (t : Tree) (p : Nat) (xs : List Nat) :
    xs.length ≤ costFrom t p xs := length_le_costFrom t p xs

/-- Exact relation between movement distance, depths, and the lowest common
ancestor. This is the identity used in §1.2 of the lazy-finger paper. -/
theorem lca_identity (t : Tree) (x y : Nat) :
    distance t x y + 2 * lcaDepth t x y =
      Tree.depth t x + Tree.depth t y := distance_add_twice_lca t x y

/-- Zero movement identifies equal keys on the valid key domain. -/
theorem zero_distance (t : Tree) (x y : Nat) (hx : x < t.size) (hy : y < t.size) :
    distance t x y = 0 ↔ x = y := distance_eq_zero_iff t x y hx hy

/-- The optimal benchmark is attained by an actual BST shape. This is an
existence result, not the paper's efficient construction algorithm. -/
theorem optimal_attained (n : Nat) (xs : List Nat) :
    ∃ t : Tree, t.size = n ∧ cost t xs = optimalCost n xs := optimalCost_attained n xs

theorem optimal_le (t : Tree) (xs : List Nat) : optimalCost t.size xs ≤ cost t xs :=
  optimalCost_le t xs

/-- First inequality of the hierarchy, against every fixed root-finger tree. -/
theorem optimal_root_finger (t : Tree) (xs : List Nat) :
    optimalCost t.size xs ≤ 2 * StaticTree.cost t xs := optimalCost_le_twice_static t xs

theorem optimal_request_charge (n : Nat) (xs : List Nat) :
    xs.length ≤ optimalCost n xs := length_le_optimalCost n xs

/-- Tree-to-weights direction of the characterization in §3 of
arXiv:1304.6897, with explicit constants and normalized request charges.
One positive weighting works for every valid pair and every valid sequence
on this tree. The converse weights-to-tree direction is separate. -/
theorem tree_weights (t : Tree) :
    ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
      (∀ x y, x < t.size → y < t.size →
        WeightedFinger.charge w x y ≤ 3 + 2 * (distance t x y : ℝ)) ∧
      (∀ p xs, p < t.size → (∀ x ∈ xs, x < t.size) →
        WeightedFinger.costFrom w p xs ≤ 3 * (costFrom t p xs : ℝ)) :=
  exists_weights_for_tree t

/-- The search path includes exactly the proper ancestors and the key itself. -/
theorem ancestor_count (t : Tree) (lo x : Nat) (hx : lo ≤ x ∧ x < lo + t.size) :
    (t.searchPath lo x).length = Tree.depth t (x - lo) + 1 :=
  searchPath_length t lo x hx

/-- The shared ancestors are the ancestors of the LCA, including the LCA. -/
theorem common_ancestor_count (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    ((t.searchPath lo x).toFinset ∩ (t.searchPath lo y).toFinset).card =
      lcaDepth t (x - lo) (y - lo) + 1 := common_ancestors_card t lo x y hx hy

/-- Distance is the count of ancestors belonging to exactly one endpoint. -/
theorem distance_events (t : Tree) (lo x y : Nat)
    (hx : lo ≤ x ∧ x < lo + t.size) (hy : lo ≤ y ∧ y < lo + t.size) :
    (distance t (x - lo) (y - lo) : ℝ) =
      ∑ a ∈ Finset.Ico lo (lo + t.size),
        ((if a ∈ t.searchPath lo x then (1 : ℝ) else 0) +
         (if a ∈ t.searchPath lo y then (1 : ℝ) else 0) -
         2 * (if a ∈ t.searchPath lo x ∧ a ∈ t.searchPath lo y then (1 : ℝ) else 0)) :=
  distance_ancestor_sum t lo x y hx hy

/-- Weights-to-tree direction of the lazy-finger characterization, with an
explicit initial finger and normalized request charges. A single fixed tree
serves the entire sequence; its choice may depend on the weights and sequence. -/
theorem tree_for_weights (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (hw : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t.size = n ∧
      (costFrom t p xs : ℝ) ≤ 4 * WeightedFinger.costFrom w p xs :=
  exists_tree_for_weights w n p xs hw hp valid

/-- The minimum over fixed trees with a specified initial finger is attained. -/
theorem optimal_from_attained (n p : Nat) (xs : List Nat) :
    ∃ t : Tree, t.size = n ∧ costFrom t p xs = optimalCostFrom n p xs :=
  optimalCostFrom_attained n p xs

/-- Weight/tree characterization with the same specified initial key on both
sides. The tree minimum is attained; the weight benchmark is an infimum. -/
theorem characterization_from (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    WeightedFinger.optimalCostFrom n p xs ≤ 3 * (optimalCostFrom n p xs : ℝ) ∧
      (optimalCostFrom n p xs : ℝ) ≤ 4 * WeightedFinger.optimalCostFrom n p xs :=
  optimal_from_characterization n p xs hp valid

/-- Replacing a fixed tree's initial finger by its root costs at most `n` once. -/
theorem initialization (t : Tree) (p : Nat) (xs : List Nat)
    (hp : p < t.size) (valid : ∀ x ∈ xs, x < t.size) :
    costFrom t p xs ≤ t.size + cost t xs ∧ cost t xs ≤ t.size + costFrom t p xs :=
  initialization_bounds t p xs hp valid

/-- Root-start characterization with explicit initialization terms. -/
theorem characterization_root (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    WeightedFinger.optimalCostFrom n p xs ≤ 3 * ((optimalCost n xs : ℝ) + n) ∧
      (optimalCost n xs : ℝ) ≤ n + 4 * WeightedFinger.optimalCostFrom n p xs :=
  optimal_root_characterization n p xs hp valid

/-- Adding the startup allowance `n` makes the benchmarks factor-four equivalent. -/
theorem characterization (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (optimalCost n xs : ℝ) + n ≤ 4 * (WeightedFinger.optimalCostFrom n p xs + n) ∧
      WeightedFinger.optimalCostFrom n p xs + n ≤ 4 * ((optimalCost n xs : ℝ) + n) :=
  characterization_with_startup n p xs hp valid

/-- When `m ≥ n`, no separate additive startup term is needed. -/
theorem characterization_long_sequence (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (long : n ≤ xs.length) :
    WeightedFinger.optimalCostFrom n p xs ≤ 6 * (optimalCost n xs : ℝ) ∧
      (optimalCost n xs : ℝ) ≤ 5 * WeightedFinger.optimalCostFrom n p xs :=
  characterization_long n p xs hp valid long

/-- Both pairwise and sequence comparisons use the same positive weights. -/
theorem tree_weights_two_sided (t : Tree) :
    ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
      (∀ x y, x < t.size → y < t.size →
        1 + (distance t x y : ℝ) ≤ WeightedFinger.charge w x y ∧
        WeightedFinger.charge w x y ≤ 3 + 2 * (distance t x y : ℝ)) ∧
      (∀ p xs, p < t.size → (∀ x ∈ xs, x < t.size) →
        (costFrom t p xs : ℝ) ≤ WeightedFinger.costFrom w p xs ∧
        WeightedFinger.costFrom w p xs ≤ 3 * (costFrom t p xs : ℝ)) :=
  exists_two_sided_weights t

end RotationBST.LazyFinger.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Results`: 22 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Rotation.Search.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.WeightedFinger.Definitions.Abstract]
