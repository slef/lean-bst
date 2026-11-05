module

public import RotationBST.Bounds.LazyFinger.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.LazyFingerWeights

private def leaf : Tree := .node .nil .nil
private def balanced : Tree := .node leaf leaf

-- Opposite children and a repeated request use one common weighting.
example : ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
    (3 ≤ WeightedFinger.charge w 0 2 ∧ WeightedFinger.charge w 0 2 ≤ 7) ∧
    (7 ≤ WeightedFinger.costFrom w 0 [2, 0, 0] ∧ WeightedFinger.costFrom w 0 [2, 0, 0] ≤ 21) := by
  obtain ⟨w, positive, pairs, sequences⟩ := LazyFinger.Results.tree_weights_two_sided balanced
  have pair := pairs 0 2 (by decide) (by decide)
  have sequence := sequences 0 [2, 0, 0] (by decide)
    (by intro x member; simp at member; rcases member with rfl | rfl <;> decide)
  refine ⟨w, positive, ?_, ?_⟩
  · norm_num [balanced, leaf, LazyFinger.distance, Tree.depth, Tree.size] at pair
    exact pair
  · norm_num [balanced, leaf, LazyFinger.costFrom, LazyFinger.distance, Tree.depth, Tree.size] at sequence
    exact sequence

-- Request normalization is retained when the movement is zero.
example : ∃ w : Nat → ℝ, (∀ x, 0 < w x) ∧
    1 ≤ WeightedFinger.charge w 0 0 ∧ WeightedFinger.charge w 0 0 ≤ 3 := by
  obtain ⟨w, positive, pairs, _⟩ := LazyFinger.Results.tree_weights_two_sided leaf
  exact ⟨w, positive, by simpa [leaf, LazyFinger.distance, Tree.depth, Tree.size] using pairs 0 0 (by decide) (by decide)⟩

end RotationBST.Tests.LazyFingerWeights
