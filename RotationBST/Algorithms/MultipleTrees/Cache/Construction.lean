module

public import RotationBST.Algorithms.MultipleTrees.Cache.Definitions.Abstract
public import RotationBST.Algorithms.MultipleTrees.Selection.Proofs
public import RotationBST.Models.Labelled.Search.Depth
public import RotationBST.Structures.WeightedSearch.Regularization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

theorem cacheKeys_perm (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheKeys n capacity frequency).Perm (selected n capacity frequency) := List.mergeSort_perm _ _

theorem cacheKeys_length (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheKeys n capacity frequency).length = min capacity n :=
  (cacheKeys_perm n capacity frequency).length_eq.trans (selected_length n capacity frequency)

theorem cacheKeys_ordered (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheKeys n capacity frequency).Pairwise (· < ·) := by
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (by intro a b c first last; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (selected n capacity frequency)
  have weak : (cacheKeys n capacity frequency).Pairwise (· ≤ ·) := by
    simpa only [cacheKeys, decide_eq_true_eq] using sorted
  exact (weak.sortedLE.sortedLT_of_nodup
    ((cacheKeys_perm n capacity frequency).nodup_iff.mpr (selected_distinct n capacity frequency))).pairwise

theorem cacheTree_erase (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).erase =
      WeightedSearch.balancedBuild ((cacheKeys n capacity frequency).map frequency) :=
  Tree.labelWith_erase _ _

theorem cacheTree_size (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).erase.size = min capacity n := by
  rw [cacheTree_erase, WeightedSearch.balanced_size, List.length_map, cacheKeys_length]

theorem cacheTree_inorder (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).inorder = cacheKeys n capacity frequency := by
  apply Tree.labelWith_inorder
  rw [WeightedSearch.balanced_size, List.length_map]

theorem cacheTree_ordered (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).Ordered := by
  apply Tree.labelWith_ordered
  · rw [WeightedSearch.balanced_size, List.length_map]
  · exact cacheKeys_ordered n capacity frequency

theorem cacheTree_lookup (n capacity : Nat) (frequency : Nat → Nat) (x : Nat) :
    (LabelledTree.lookup (cacheTree n capacity frequency) x).1 = true ↔
      x ∈ selected n capacity frequency := by
  rw [LabelledTree.lookup_correct _ (cacheTree_ordered n capacity frequency), cacheTree_inorder]
  exact (cacheKeys_perm n capacity frequency).mem_iff

end RotationBST.MultipleTrees
