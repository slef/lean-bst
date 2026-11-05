module

public import RotationBST.Algorithms.GreedyASS.Performance.Simulation
public import RotationBST.Bounds.LazyFinger.Consequences.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Performance

/-- Corollary 1 for the geometric sweep, with a unit charge per request
and an explicit predecessor for the first request. -/
theorem dynamic (n p : Nat) (xs : List Nat) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (rowCost greedySweep 0 ∅ xs : ℝ) ≤ 480 * Bounds.dynamicFingerCostFrom p xs + 15 * n := by
  simpa only [LazyFinger.Consequences.Results.unit_weights] using
    weighted (fun _ => 1) n p xs (by intros; norm_num) hp valid

/-- The BST policy is chosen before every positive weighting and every
initial predecessor, and it serves all valid streams from every initial BST. -/
theorem bst_weighted (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ w : Nat → ℝ, (∀ k < n, 0 < w k) →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        (algorithm.totalCost initial xs : ℝ) ≤ 2889120 * WeightedFinger.costFrom w p xs + 96303 * n := by
  obtain ⟨algorithm, bound⟩ := bst n
  refine ⟨algorithm, ?_⟩
  intro initial size p hp w positive xs valid
  have optimized := (bound initial size xs valid).2 p hp
  have comparison := WeightedFinger.Results.optimal_le w n p xs positive hp valid
  linarith

theorem bst_dynamic (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        (algorithm.totalCost initial xs : ℝ) ≤ 2889120 * Bounds.dynamicFingerCostFrom p xs + 96303 * n := by
  obtain ⟨algorithm, bound⟩ := bst_weighted n
  refine ⟨algorithm, ?_⟩
  intro initial size p hp xs valid
  simpa only [LazyFinger.Consequences.Results.unit_weights] using
    bound initial size p hp (fun _ => 1) (by intros; norm_num) xs valid

/-- The all-weightings statement also holds for actual charged pointer
execution; the infimum in the optimized result need not be attained. -/
theorem pointer_weighted (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ p, p < n → ∀ w : Nat → ℝ, (∀ k < n, 0 < w k) →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution initial xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ∧
        ((Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 : ℝ) ≤
          92444640 * WeightedFinger.costFrom w p xs + 3081471 * n := by
  obtain ⟨algorithm, bound⟩ := pointer n
  refine ⟨algorithm, ?_⟩
  intro initial size p hp w positive xs valid
  obtain ⟨execution, _, optimized⟩ := bound initial size xs valid
  refine ⟨execution, ?_⟩
  have weightedBound := optimized p hp
  have comparison := WeightedFinger.Results.optimal_le w n p xs positive hp valid
  linarith

end RotationBST.Geometric.GreedyASS.Performance
