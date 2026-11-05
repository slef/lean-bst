module

public import RotationBST.Algorithms.GreedyASS.Potential.Amortized.Stream
public import RotationBST.Algorithms.Simulation.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Amortized
open Reference

/-- One causal BST policy, chosen without a reference tree or request
sequence, has the leaf-oriented lazy-finger bound for every reference shape.
The cost counts requests and rotations and includes initialization. -/
theorem bst (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ reference : Tree, leaves reference = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost initial xs ≤
          144456 * referenceCost reference 0 xs + 96303 * n := by
  obtain ⟨algorithm, bound⟩ := Simulation.Results.normalized_simulation n (greedyASS n)
  refine ⟨algorithm, ?_⟩
  intro initial size reference population xs valid
  have simulated := bound initial size xs valid
  have geometric := cost reference 0 xs (by simpa [population] using valid)
  simp only [greedyASS] at simulated
  rw [population] at geometric
  omega

/-- The same sequence-independent guarantee in the pointer model, charging
navigation, rotations, root resets, and initialization through the existing
causal geometric simulation. -/
theorem pointer (n : Nat) :
    ∃ algorithm : Algorithm, ∀ initial : Tree, initial.size = n →
      ∀ reference : Tree, leaves reference = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution initial xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ∧
        (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial initial) xs).2 ≤
          4622232 * referenceCost reference 0 xs + 3081471 * n := by
  obtain ⟨algorithm, bound⟩ := Simulation.Results.pointer_simulation n (greedyASS n)
  refine ⟨algorithm, ?_⟩
  intro initial size reference population xs valid
  obtain ⟨execution, simulated⟩ := bound initial size xs valid
  refine ⟨execution, ?_⟩
  have geometric := cost reference 0 xs (by simpa [population] using valid)
  simp only [greedyASS] at simulated
  rw [population] at geometric
  omega

end RotationBST.Geometric.GreedyASS.Potential.Amortized
