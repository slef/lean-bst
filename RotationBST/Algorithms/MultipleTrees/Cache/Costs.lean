module

public import RotationBST.Algorithms.MultipleTrees.Cache.Construction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Cache misses obey the same uniform bound as hits, including rows whose
observed successor frequencies are all zero. -/
theorem cacheTree_uniform (n capacity : Nat) (frequency : Nat → Nat) (x : Nat)
    (nonempty : 0 < min capacity n) :
    ((LabelledTree.lookup (cacheTree n capacity frequency) x).2 : ℝ) ≤
      Real.logb 2 (2 * ((min capacity n : Nat) : ℝ)) + 1 := by
  apply LabelledTree.lookup_cost_le
  · apply Real.logb_nonneg (by norm_num)
    have : (1 : ℝ) ≤ min capacity n := by exact_mod_cast nonempty
    linarith
  · intro i valid
    rw [cacheTree_erase] at valid ⊢
    have index : i < ((cacheKeys n capacity frequency).map frequency).length := by
      simpa only [WeightedSearch.balanced_size] using valid
    have depth := WeightedSearch.balanced_depth_uniform _ i index
    simpa only [List.length_map, cacheKeys_length] using depth

/-- A successful comparison search inherits the biased weighted-median bound.
The total is the mass of the entire successor row, not just its cached prefix. -/
theorem cacheTree_weighted (n capacity : Nat) (frequency : Nat → Nat) (x : Nat)
    (stored : x ∈ selected n capacity frequency) (positive : 0 < frequency x) :
    ((LabelledTree.lookup (cacheTree n capacity frequency) x).2 : ℝ) ≤
      Real.logb 2 (3 * (((List.range n).map frequency).sum : ℝ) / frequency x) + 1 := by
  have member := (cacheKeys_perm n capacity frequency).mem_iff.mpr stored
  let keys := cacheKeys n capacity frequency
  let weights := keys.map frequency
  let i := keys.idxOf x
  have valid : i < keys.length := List.idxOf_lt_length_of_mem member
  have label : keys[i] = x := List.getElem_idxOf valid
  have weightValid : i < weights.length := by simpa only [weights, List.length_map] using valid
  have entry : weights[i] = frequency x := by simp only [weights, List.getElem_map, label]
  have size : keys.length = (WeightedSearch.balancedBuild weights).size := by
    simp only [WeightedSearch.balanced_size, weights, List.length_map]
  have query := LabelledTree.lookup_rank_cost (WeightedSearch.balancedBuild weights)
    keys size (cacheKeys_ordered n capacity frequency) i valid
  rw [label] at query
  have depth := WeightedSearch.balanced_depth_weighted weights i weightValid (by rw [entry]; exact positive)
  rw [entry] at depth
  have mass : weights.sum ≤ ((List.range n).map frequency).sum := by
    have same := ((cacheKeys_perm n capacity frequency).map frequency).sum_eq
    exact same.le.trans (selected_mass_le n capacity frequency)
  have weightPositive : (0 : ℝ) < frequency x := by exact_mod_cast positive
  have present : frequency x ≤ weights.sum := by
    rw [← entry]
    exact List.le_sum_of_mem (List.getElem_mem weightValid)
  have sumPositive : (0 : ℝ) < weights.sum := by exact_mod_cast (lt_of_lt_of_le positive present)
  have ratio : 3 * (weights.sum : ℝ) / frequency x ≤
      3 * (((List.range n).map frequency).sum : ℝ) / frequency x := by
    apply div_le_div_of_nonneg_right _ weightPositive.le
    have cast : (weights.sum : ℝ) ≤ ((List.range n).map frequency).sum := by exact_mod_cast mass
    linarith
  have logarithm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity) ratio
  change (LabelledTree.lookup (cacheTree n capacity frequency) x).2 = _ at query
  rw [query, Nat.cast_add, Nat.cast_one]
  linarith

end RotationBST.MultipleTrees
