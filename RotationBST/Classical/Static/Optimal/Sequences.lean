module

public import RotationBST.Classical.Static.Optimal.Weights
public import RotationBST.Models.Rotation.Shapes
public import RotationBST.Classical.Static.Balanced
public import RotationBST.Bounds.StaticTree.Abstract
import Mathlib.Tactic

@[expose] public section

/-! The optimal tree for request counts is the best static tree for the
sequence: below every fixed tree, between a third of the entropy bound and the
entropy bound, and below the balanced tree. -/
namespace RotationBST.Classical.Static
open _root_.RotationBST.Tree (balanced)

theorem optTree_counts_size (n : Nat) (xs : List Nat) : (optTree (counts n xs)).size = n := by
  rw [optTree_size, counts_length]

theorem optTree_static (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    StaticTree.cost (optTree (counts n xs)) xs = optCost (counts n xs) := by
  have hs := optTree_counts_size n xs
  rw [staticCost_eq_weightedCost _ xs (by rw [hs]; exact valid), hs, optTree_cost]

theorem optCost_le_static (n : Nat) (xs : List Nat) (t : Tree) (ht : t.size = n)
    (valid : ∀ x ∈ xs, x < n) : optCost (counts n xs) ≤ StaticTree.cost t xs := by
  rw [staticCost_eq_weightedCost t xs (by rw [ht]; exact valid), ht]
  exact optCost_le _ t (by rw [counts_length, ht])

theorem optCost_le_entropy (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (optCost (counts n xs) : ℝ) ≤ Bounds.staticCost n xs := by
  obtain ⟨t, ht, hc⟩ := StaticTree.Results.entropy_upper_bound n xs valid
  exact (Nat.cast_le.mpr (optCost_le_static n xs t ht valid)).trans hc

theorem entropy_le_optCost (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    Bounds.staticCost n xs ≤ 3 * (optCost (counts n xs) : ℝ) := by
  have hs := optTree_counts_size n xs
  have := StaticTree.Results.entropy_lower_bound (optTree (counts n xs)) xs (by rw [hs]; exact valid)
  rwa [hs, optTree_static n xs valid] at this

theorem optCost_le_balanced (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    optCost (counts n xs) ≤ xs.length * (Nat.log2 n + 1) :=
  (optCost_le_static n xs (balanced n) (Tree.balanced_size n) valid).trans (balanced_cost n xs valid)

end RotationBST.Classical.Static
