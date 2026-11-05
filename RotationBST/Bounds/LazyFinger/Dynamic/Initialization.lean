module

public import RotationBST.Bounds.LazyFinger.Dynamic.Simulation
public import RotationBST.Models.Pointer.Reshape

@[expose] public section
namespace RotationBST.LazyFinger

/-- Start the dynamic BST in any prescribed tree on the same keys. Reshaping
is charged to the first request; the empty sequence needs no initialization. -/
theorem dynamic_reference_tree (s t : Tree) (xs : List Nat) (same : s.size = t.size)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 16 * s.size + 464 * cost t xs := by
  cases xs with
  | nil => exact ⟨s, 0, .nil, Nat.zero_le _⟩
  | cons x xs =>
    obtain ⟨u, k, execution, bound⟩ := dynamic_execution t (x :: xs) valid
    obtain ⟨j, startup, trace⟩ := Pointer.reshape s t same
    exact ⟨u, j + k, execution.prepend trace, by omega⟩

/-- The dynamic/lazy-finger inequality in the hierarchy (Theorem 6 of
arXiv:1304.6897), with normalized request charges and explicit initialization.
The initial dynamic tree is arbitrary and fixed before choosing the optimal
reference tree. The resulting execution is an offline existence witness. -/
theorem dynamic_optimal (s : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < s.size) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 16 * s.size + 464 * optimalCost s.size xs := by
  obtain ⟨t, size, optimum⟩ := optimalCost_attained s.size xs
  obtain ⟨u, k, execution, bound⟩ := dynamic_reference_tree s t xs size.symm
    (by simpa only [size] using valid)
  exact ⟨u, k, execution, by simpa only [optimum] using bound⟩

/-- If there are at least as many requests as keys, startup is absorbed into
the normalized optimal lazy-finger cost. -/
theorem dynamic_optimal_long (s : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < s.size) (long : s.size ≤ xs.length) :
    ∃ u k, Pointer.Execution s xs u k ∧ k ≤ 480 * optimalCost s.size xs := by
  obtain ⟨u, k, execution, bound⟩ := dynamic_optimal s xs valid
  have charge := length_le_optimalCost s.size xs
  exact ⟨u, k, execution, by omega⟩

end RotationBST.LazyFinger
