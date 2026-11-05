module

public import RotationBST.Algorithms.GreedyASS.Performance.Geometric
public import RotationBST.Algorithms.Simulation.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Performance

/-- Theorems 4.1 and 4.2 for one causal BST policy. Policy selection precedes
the initial tree, request sequence, and weighted benchmark's predecessor.
Initialization is paid once and total cost includes request charges. -/
theorem bst (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost initial xs ≤ 722280 * LazyFinger.optimalCost n xs + 96303 * n ∧
        ∀ p, p < n → (algorithm.totalCost initial xs : ℝ) ≤
          2889120 * WeightedFinger.optimalCostFrom n p xs + 96303 * n := by
  obtain ⟨algorithm, bound⟩ := Simulation.Results.normalized_simulation n (greedyASS n)
  refine ⟨algorithm, ?_⟩
  intro initial size xs valid
  have simulated := bound initial size xs valid
  simp only [greedyASS] at simulated
  constructor
  · have geometric := lazy_optimal n xs valid
    omega
  · intro p hp
    have geometric := weighted_optimal n p xs hp valid
    have simulatedReal : (algorithm.totalCost initial xs : ℝ) ≤
        6019 * (rowCost greedySweep 0 ∅ xs : ℝ) + 6018 * n := by exact_mod_cast simulated
    linarith

/-- An actual pointer execution satisfies both optimized bounds. The
execution includes navigation, rotations, and initialization, and its
policy is independent of every reference tree and weighting. -/
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
            92444640 * WeightedFinger.optimalCostFrom n p xs + 3081471 * n := by
  obtain ⟨algorithm, bound⟩ := Simulation.Results.pointer_simulation n (greedyASS n)
  refine ⟨algorithm, ?_⟩
  intro initial size xs valid
  obtain ⟨execution, simulated⟩ := bound initial size xs valid
  simp only [greedyASS] at simulated
  refine ⟨execution, ?_, ?_⟩
  · have geometric := lazy_optimal n xs valid
    omega
  · intro p hp
    have geometric := weighted_optimal n p xs hp valid
    have simulatedReal :
        ((Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 : ℝ) ≤
          192593 * (rowCost greedySweep 0 ∅ xs : ℝ) + 192576 * n := by exact_mod_cast simulated
    linarith

end RotationBST.Geometric.GreedyASS.Performance
