module

public import RotationBST.Algorithms.Simulation.Supernode.Policy.Uniform
public import RotationBST.Models.Pointer.Lazy.Online.Abstract

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- Each legal geometric row includes its request, so point count pays for
one search charge per request as well as for the simulated rotations. -/
theorem rowCost_length {n : Nat} (A : OnlineAlgorithm n) (xs : List Nat)
    {time : Nat} {P : Finset Point} (history : History n time P) (satisfied : ASS P)
    (bounds : ∀ x ∈ xs, x < n) : xs.length ≤ rowCost A.step time P xs := by
  induction xs generalizing time P with
  | nil => simp [rowCost]
  | cons request rest ih =>
    have legal := A.correct time request P history satisfied (bounds request (List.mem_cons_self ..))
    have positive := Finset.card_pos.mpr ⟨request, legal.1⟩
    have tail := ih (history_extend history legal) legal.2.2
      (fun x member => bounds x (List.mem_cons_of_mem _ member))
    simp only [List.length_cons, rowCost]
    omega

/-- Uniform online simulation in normalized BST cost, including one unit for
every request. -/
theorem uniform_online_total (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        algorithm.totalCost tree xs ≤ 6019 * rowCost A.step 0 ∅ xs + 6018 * n := by
  obtain ⟨algorithm, correct⟩ := uniform_online_policy n A
  refine ⟨algorithm, ?_⟩
  intro tree size xs bounds
  have rotations := correct tree size xs bounds
  have requests := rowCost_length A xs (time := 0) (P := ∅) (by intro p member; simp at member)
    (by intro p member; simp at member) bounds
  simp only [Algorithm.totalCost]
  omega

/-- The same causal simulation has a conventional single-pointer execution.
The pointer strategy is fixed before the request sequence; deferred work is
handled by the existing online rotation-to-pointer transformer. -/
theorem uniform_online_pointer (n : Nat) (A : OnlineAlgorithm n) :
    ∃ algorithm : Algorithm, ∀ tree : Tree, tree.size = n →
      ∀ xs : List Nat, (∀ x ∈ xs, x < n) →
        Pointer.Execution tree xs
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).1.current
          (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).2 ∧
        (Pointer.Lazy.Online.run algorithm [] (Pointer.Lazy.Online.initial tree) xs).2 ≤
          192593 * rowCost A.step 0 ∅ xs + 192576 * n := by
  obtain ⟨algorithm, correct⟩ := uniform_online_policy n A
  refine ⟨algorithm, ?_⟩
  intro tree size xs bounds
  have rotations := correct tree size xs bounds
  have requests := rowCost_length A xs (time := 0) (P := ∅) (by intro p member; simp at member)
    (by intro p member; simp at member) bounds
  have simulation := (Pointer.Lazy.Online.Results.simulation algorithm [] tree xs
    (fun x member => by rw [size]; exact bounds x member))
  refine ⟨simulation.1, ?_⟩
  have pointer := simulation.2.2
  change _ ≤ 6018 * rowCost A.step 0 ∅ xs + 6018 * n at rotations
  change _ + 32 * _ ≤ 32 * algorithm.cost tree xs + 17 * xs.length at pointer
  omega

end RotationBST.Geometric.Online.Supernode
