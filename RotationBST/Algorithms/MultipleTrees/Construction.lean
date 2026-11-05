module

public import RotationBST.Algorithms.MultipleTrees.Definitions.Abstract
public import RotationBST.Algorithms.MultipleTrees.Cache.Costs
public import RotationBST.Models.LinkedSearch.Correctness
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

theorem rootAddress_valid (n : Nat) (positive : 0 < n) (x : Nat) (valid : x < n) :
    rootAddress n positive x = (⟨x, valid⟩ : Fin n) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt valid

theorem selected_full (n : Nat) (frequency : Nat → Nat) (x : Nat) :
    x ∈ selected n n frequency ↔ x < n := by
  have length : (ranking n frequency).length = n :=
    (ranking_perm n frequency).length_eq.trans List.length_range
  have full : (ranking n frequency).take n = ranking n frequency := by
    exact List.take_of_length_le length.le
  rw [selected, full, (ranking_perm n frequency).mem_iff, List.mem_range]

theorem fallbackTree_size (n : Nat) : (fallbackTree n).erase.size = n := by
  simp only [fallbackTree, cacheTree_size, Nat.min_self]

theorem fallbackTree_lookup (n x : Nat) :
    (LabelledTree.lookup (fallbackTree n) x).1 = true ↔ x < n := by
  rw [fallbackTree, cacheTree_lookup, selected_full]

/-- Exact node storage: `n` caches of `min(capacity,n)` nodes, plus one `n`-node
fallback. The preprocessing frequencies are absent from this count and store. -/
theorem build_nodes (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) :
    (build n capacity positive frequency).nodes = n * min capacity n + n := by
  simp only [LinkedSearch.Store.nodes, build, LinkedSearch.attach_erase, cacheTree_size,
    fallbackTree_size, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Explicit word count includes successor links, child pointers, and roots. -/
theorem build_words (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat) :
    (build n capacity positive frequency).words = 4 * (n * min capacity n + n) + n + 1 := by
  simp only [LinkedSearch.Store.words, build_nodes, Fintype.card_fin]

theorem build_space (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) : (build n capacity positive frequency).words ≤ 10 * n * capacity := by
  rw [build_words]
  have small : min capacity n ≤ capacity := Nat.min_le_left _ _
  have product : n * min capacity n ≤ n * capacity := Nat.mul_le_mul_left n small
  have rootSpace : n ≤ n * capacity := by nlinarith
  nlinarith

end RotationBST.MultipleTrees
