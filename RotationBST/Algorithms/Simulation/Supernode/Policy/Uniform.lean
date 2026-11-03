module

public import RotationBST.Algorithms.Simulation.Supernode.Policy.Bound
public import RotationBST.Models.Online.Reset

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- A single policy works for every initial tree in the universe. Initial
shape conversion is charged once, independently of sequence length. -/
theorem uniform_online_policy (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.cost tree xs ≤ 6018 * rowCost A.step 0 ∅ xs + 6018 * n := by
  obtain ⟨reference, size⟩ : ∃ tree : Tree, tree.size = n :=
    ⟨(initialNested n).tree, initialNested_size n⟩
  subst n
  obtain ⟨algorithm, bound⟩ := online_policy reference A
  refine ⟨resetAlgorithm algorithm reference, ?_⟩
  intro tree size xs valid
  have reset := resetAlgorithm_cost algorithm reference tree size xs
  have simulated := bound xs valid
  omega

end RotationBST.Geometric.Online.Supernode
