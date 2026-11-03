module

public import RotationBST.Algorithms.Simulation.Supernode.Simulation.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Transition.Access
public import RotationBST.Models.Geometric.Online.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- Compose row accesses while deferring restoration to the next access.
The final restoration is included in the bound, so every rotation is paid
and the potential telescopes across arbitrarily many rows. -/
theorem runState_execution {n : Nat} (A : OnlineAlgorithm n) (xs : List Nat)
    {time : Nat} {P : Finset Point} {state : Nested} {actual : Tree} {debt : Nat}
    (history : History n time P) (satisfied : ASS P)
    (represented : Represents P 0 state) (size : state.tree.size = n)
    (restore : Rotations actual state.tree debt) (bounds : ∀ x ∈ xs, x < n) :
    Represents (fill A.step time P xs) 0 (runState A.step time P state xs) ∧
      ∃ target cost remaining,
        Execution actual xs target cost ∧
        Rotations target (runState A.step time P state xs).tree remaining ∧
        cost + remaining + (runState A.step time P state xs).credit ≤
          debt + state.credit + 6018 * rowCost A.step time P xs := by
  induction xs generalizing time P state actual debt with
  | nil => exact ⟨represented, actual, 0, debt, .nil, restore, by simp [runState, rowCost]⟩
  | cons request rest ih =>
    have legal := A.correct time request P history satisfied (bounds request (List.mem_cons_self ..))
    obtain ⟨nextValid, served, accessCost, restoreCost, access, restored, budget⟩ :=
      nextState_access history legal represented size
    have nextSize : (nextState state (A.step time request P)).tree.size = n := by
      have first := access.1.size_eq
      have second := restored.size_eq
      omega
    obtain ⟨finalValid, target, cost, remaining, execution, finalRestore, total⟩ :=
      ih (history_extend history legal) legal.2.2 nextValid nextSize restored
        (fun x member => bounds x (List.mem_cons_of_mem _ member))
    refine ⟨finalValid, target, debt + accessCost + cost, remaining,
      .cons ⟨restore.append access.1, access.2⟩ execution, finalRestore, ?_⟩
    simp only [runState, rowCost]
    simp only [Nat.mul_add]
    omega

end RotationBST.Geometric.Online.Supernode
