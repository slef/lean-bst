module

public import RotationBST.Algorithms.Simulation.Supernode.Policy.Machine

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

noncomputable def Machine.replay {n : Nat} (A : OnlineAlgorithm n) (initial : Machine n)
    (past : List Nat) : Machine n :=
  past.foldl (fun machine request => if bound : request < n then (machine.advance A request bound).1 else machine) initial

theorem Machine.replay_append {n : Nat} (A : OnlineAlgorithm n) (initial : Machine n)
    (past : List Nat) (request : Nat) (bound : request < n) :
    initial.replay A (past ++ [request]) = ((initial.replay A past).advance A request bound).1 := by
  simp only [Machine.replay, List.foldl_append, List.foldl_cons, List.foldl_nil, dite_eq_left bound]

/-- Replay fixes a single choice for every request prefix. Unexpected trees
use the standard move-to-root rule so the interface is correct everywhere. -/
noncomputable def simulatedAlgorithm {n : Nat} (A : OnlineAlgorithm n) (initial : Machine n) : Algorithm where
  step past tree request :=
    if matching : tree = (initial.replay A past).actual ∧ request < n then
      let result := (initial.replay A past).advance A request matching.2
      (result.1.actual, result.2)
    else moveToRoot tree request
  correct past tree request bound := by
    dsimp only
    split
    · rename_i matching
      have access := ((initial.replay A past).advance_spec A request matching.2).2.2.2.1
      simpa only [matching.1] using access
    · exact (moveToRoot_correct tree request bound).1

theorem simulatedAlgorithm_step {n : Nat} (A : OnlineAlgorithm n) (initial : Machine n)
    (past : List Nat) (request : Nat) (bound : request < n) :
    (simulatedAlgorithm A initial).step past (initial.replay A past).actual request =
      (((initial.replay A past).advance A request bound).1.actual,
        ((initial.replay A past).advance A request bound).2) := by
  simp [simulatedAlgorithm, bound]

/-- One fixed policy has the telescoping potential bound for every continuation
of every prefix. No execution is chosen after seeing that continuation. -/
theorem simulatedAlgorithm_budget {n : Nat} (A : OnlineAlgorithm n) (initial : Machine n)
    (past xs : List Nat) (bounds : ∀ x ∈ xs, x < n) :
    (simulatedAlgorithm A initial).runFrom past (initial.replay A past).actual xs =
      ((initial.replay A (past ++ xs)).actual,
        ((simulatedAlgorithm A initial).runFrom past (initial.replay A past).actual xs).2) ∧
    ((simulatedAlgorithm A initial).runFrom past (initial.replay A past).actual xs).2 +
        (initial.replay A (past ++ xs)).debt + (initial.replay A (past ++ xs)).stored.credit ≤
      (initial.replay A past).debt + (initial.replay A past).stored.credit +
        6018 * rowCost A.step (initial.replay A past).time (initial.replay A past).points xs := by
  induction xs generalizing past with
  | nil => simp [Algorithm.runFrom, rowCost]
  | cons request rest ih =>
    have bound := bounds request (List.mem_cons_self ..)
    have recursive := ih (past ++ [request]) (fun x member => bounds x (List.mem_cons_of_mem _ member))
    have step := (initial.replay A past).advance_spec A request bound
    have next := Machine.replay_append A initial past request bound
    have append : (past ++ [request]) ++ rest = past ++ request :: rest := by simp only [List.append_assoc, List.singleton_append]
    rw [append, next] at recursive
    simp only [Algorithm.runFrom, simulatedAlgorithm_step A initial past request bound]
    constructor
    · rw [recursive.1]
    · have paid := step.2.2.2.2
      simp only [rowCost, Nat.mul_add]
      rw [step.1, step.2.1] at recursive
      omega

end RotationBST.Arboral.Online.Supernode
