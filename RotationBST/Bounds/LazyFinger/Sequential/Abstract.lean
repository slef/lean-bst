module

import RotationBST.Audit.Check
public import RotationBST.Bounds.LazyFinger.Sequential.AbstractBridge

@[expose] public section
namespace RotationBST.LazyFinger.Sequential.Results

/-- Every fixed tree executes repeated ordered scans in linear lazy-finger cost. -/
theorem lazy_scan (t : Tree) (rounds : Nat) :
    cost t (scans t.size rounds) ≤ 4 * rounds * t.size := scans_cost t rounds

/-- The same bound from any valid initial key. -/
theorem lazy_scan_from (t : Tree) (p rounds : Nat) (hp : p < t.size) :
    costFrom t p (scans t.size rounds) ≤ 4 * rounds * t.size := scans_costFrom t p rounds hp

/-- Every root-finger tree pays a logarithmic charge per scan request. -/
theorem root_scan (t : Tree) (rounds : Nat) :
    (rounds * t.size : Nat) * (1 + Real.logb 2 (t.size : ℝ)) ≤
      3 * (StaticTree.cost t (scans t.size rounds) : ℝ) := scans_root_lower t rounds

/-- A concrete family with any prescribed strict gap, independent of the lazy
and root-finger tree shapes, for any positive number of scans. -/
theorem strict_gap (C rounds : Nat) (hr : 0 < rounds) (lazy root : Tree)
    (hl : lazy.size = 2 ^ (12 * C)) (ht : root.size = 2 ^ (12 * C)) :
    C * cost lazy (scans (2 ^ (12 * C)) rounds) <
      StaticTree.cost root (scans (2 ^ (12 * C)) rounds) := scans_separate C rounds hr lazy root hl ht

/-- No uniform constant bounds best root-finger cost by best lazy-finger cost. -/
theorem unbounded_ratio (C : Nat) :
    ∃ n xs, 0 < n ∧ xs.length = n ∧ (∀ x ∈ xs, x < n) ∧
      ∀ t : Tree, t.size = n → C * optimalCost n xs < StaticTree.cost t xs := root_lazy_unbounded C

/-- No universe-dependent startup allowance repairs the missing constant-factor
comparison: a sufficiently long repeated scan defeats it. -/
theorem gap_beyond_startup (C : Nat) (allowance : Nat → Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ t : Tree, t.size = n → C * optimalCost n xs + allowance n < StaticTree.cost t xs :=
  root_lazy_unbounded_with_startup C allowance

theorem prefix_length (n m : Nat) : (scanPrefix n m).length = m :=
  scanPrefix_length n m

theorem prefix_valid (n m : Nat) (positive : 0 < n) : ∀ x ∈ scanPrefix n m, x < n :=
  scanPrefix_valid n m positive

theorem lazy_prefix (t : Tree) (m : Nat) (positive : 0 < t.size) (long : t.size ≤ m) :
    cost t (scanPrefix t.size m) ≤ 8 * (m / t.size) * t.size :=
  scanPrefix_cost t m positive long

theorem all_lengths_shapes (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ lazy root : Tree, lazy.size = n → root.size = n →
          C * cost lazy xs + allowance n < StaticTree.cost root xs :=
  root_lazy_all_lengths C allowance

theorem all_lengths (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ root : Tree, root.size = n →
          C * optimalCost n xs + allowance n < StaticTree.cost root xs :=
  optimal_root_lazy_all_lengths C allowance

/-- One family, fixed before the factor is chosen, has an unbounded separation
ratio as its sequence length grows. -/
theorem family (allowance : Nat → Nat) :
    ∃ sizes : Nat → Nat, ∃ requests : Nat → List Nat,
      (∀ m, 0 < sizes m ∧ (requests m).length = m ∧
        (∀ x ∈ requests m, x < sizes m)) ∧
      ∀ C, ∃ threshold, ∀ m, threshold ≤ m →
        ∀ root : Tree, root.size = sizes m →
          C * optimalCost (sizes m) (requests m) + allowance (sizes m) <
            StaticTree.cost root (requests m) := optimal_root_lazy_family allowance

end RotationBST.LazyFinger.Sequential.Results

/-- info: abstract audit passed for `RotationBST.LazyFinger.Sequential.Results`: 12 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LazyFinger.Sequential.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Sequential.Definitions.Abstract]
