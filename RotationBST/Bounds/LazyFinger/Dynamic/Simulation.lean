module

public import RotationBST.Bounds.LazyFinger.Dynamic.Multifinger
public import RotationBST.Bounds.LazyFinger.Optimal
public import RotationBST.Structures.FingerHand.Packed.Simulation.Execution

@[expose] public section
namespace RotationBST.LazyFinger

/-- A conventional dynamic BST can match a fixed-tree lazy finger up to an
absolute constant, starting from that very same tree. The empty domain is
included. This is an existence comparison of legal executions. -/
theorem dynamic_execution (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) :
    ∃ u k, Pointer.Execution t xs u k ∧ k ≤ 464 * cost t xs := by
  by_cases nonempty : 0 < t.size
  · obtain ⟨q, run⟩ := multifinger_root_execution t xs nonempty valid
    obtain ⟨after, k, _, execution, bound⟩ :=
      FingerHand.Hand.one_finger_execution 1 t nonempty run
    exact ⟨after.tree, k, execution, bound⟩
  · have empty : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have := valid x hx
      omega
    subst xs
    exact ⟨t, 0, .nil, Nat.zero_le _⟩

/-- Optimize the comparison over reference-tree shapes. The initial dynamic
tree is explicitly the chosen optimal lazy-finger tree. -/
theorem dynamic_optimal_tree (n : Nat) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < n) :
    ∃ t u k, t.size = n ∧ Pointer.Execution t xs u k ∧ k ≤ 464 * optimalCost n xs := by
  obtain ⟨t, size, optimum⟩ := optimalCost_attained n xs
  obtain ⟨u, k, execution, bound⟩ := dynamic_execution t xs (by simpa only [size] using valid)
  exact ⟨t, u, k, size, execution, by simpa only [optimum] using bound⟩

end RotationBST.LazyFinger
