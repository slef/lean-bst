module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Policy.Algorithm

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- One BST policy, fixed before the request sequence, simulates the geometric
algorithm from the supplied initial tree with linear total rotation cost. -/
theorem online_policy (tree : Tree) (A : OnlineAlgorithm tree.size) :
    ∃ algorithm : Algorithm, ∀ xs : List Nat, (∀ x ∈ xs, x < tree.size) →
      algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6016 * tree.size := by
  refine ⟨simulatedAlgorithm A (Machine.initial tree), ?_⟩
  intro xs bounds
  have initial := Machine.initial_spec tree
  have budget := (simulatedAlgorithm_budget A (Machine.initial tree) [] xs bounds).2
  simp only [Machine.replay, List.foldl_nil] at budget
  rw [initial.1, initial.2.1, initial.2.2.1] at budget
  change ((simulatedAlgorithm A (Machine.initial tree)).runFrom [] tree xs).2 ≤ _
  have initialization := initial.2.2.2
  omega

end RotationBST.Arboral.Online.Supernode
