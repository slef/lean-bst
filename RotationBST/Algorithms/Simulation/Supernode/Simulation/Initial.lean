module

public import RotationBST.Algorithms.Simulation.Supernode.Simulation.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Nested.Initial

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Initially there is one root supernode and all child gaps are empty. -/
theorem initialNested_credit (n : Nat) :
    (initialNested n).credit = intervalCredit (initialInterval n) := by
  cases initial : initialInterval n with
  | none => simp [initialNested, initial, Nested.credit, intervalCredit, intervalNodes, intervalTree, Tree.size]
  | some state => simp [initialNested, initial, Nested.credit]

/-- Any initial BST can be converted to the initial stored state, including
its entire splitting potential, with a linear initialization allowance. -/
theorem initialNested_budget (tree : Tree) :
    ∃ cost, Rotations tree (initialNested tree.size).tree cost ∧
      cost + (initialNested tree.size).credit ≤ 6016 * tree.size := by
  obtain ⟨cost, bound, steps⟩ := reset_linear tree (initialNested tree.size).tree
    (initialNested_size tree.size).symm
  have credit := intervalCredit_linear (initialInterval tree.size)
  rw [initialInterval_size, ← initialNested_credit] at credit
  exact ⟨cost, steps, by omega⟩

/-- Every run of an online geometric algorithm has a root-access execution
with linear total rotation cost, including initialization and deferred work. -/
theorem geometric_execution (tree : Tree) (A : OnlineAlgorithm tree.size) (xs : List Nat)
    (bounds : ∀ x ∈ xs, x < tree.size) :
    ∃ target cost, Execution tree xs target cost ∧
      cost ≤ 6018 * rowCost A.step 0 ∅ xs + 6016 * tree.size := by
  obtain ⟨debt, restore, initialization⟩ := initialNested_budget tree
  have history : History tree.size 0 ∅ := by intro p member; simp at member
  have satisfied : ASS ∅ := by intro a member; simp at member
  obtain ⟨_, target, cost, remaining, execution, _, budget⟩ :=
    runState_execution A xs history satisfied (initialNested_represents tree.size)
      (initialNested_size tree.size) restore bounds
  exact ⟨target, cost, execution, by omega⟩

end RotationBST.Arboral.Online.Supernode
