module

public import RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Controller.Sequences
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Rounds

theorem cuts_ordered {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) :
    (cuts worker budget restore s offset xs).Pairwise (· < ·) ∧
      ∀ i ∈ cuts worker budget restore s offset xs, offset ≤ i ∧ i < offset + xs.length := by
  induction xs generalizing s offset with
  | nil => simp [cuts]
  | cons x xs ih =>
    have rest := ih (Controller.serve worker budget restore s x).state (offset + 1)
    by_cases done : (Controller.serve worker budget restore s x).done = true
    · by_cases switched : (Controller.serve worker budget restore s x).switched = true
      · simp only [cuts, done, switched, ↓reduceIte]
        refine ⟨List.pairwise_cons.mpr ⟨?_, rest.1⟩, ?_⟩
        · intro i member
          have := rest.2 i member
          omega
        · intro i member
          rcases List.mem_cons.mp member with rfl | member
          · simp only [List.length_cons]; omega
          · have := rest.2 i member
            simp only [List.length_cons]; omega
      · simp only [cuts, done, switched, Bool.false_eq_true, ↓reduceIte]
        refine ⟨rest.1, ?_⟩
        intro i member
        have := rest.2 i member
        simp only [List.length_cons]; omega
    · simp [cuts, done]

/-- Exactly the switches in the completed operational execution are recorded. -/
theorem cuts_length {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) (offset : Nat) :
    (cuts worker budget restore s offset xs).length = switches := by
  induction execution generalizing offset with
  | nil => rfl
  | @cons s t x xs cost switches done tail ih =>
    by_cases changed : (Controller.serve worker budget restore s x).switched = true
    · simp only [cuts, done, changed, ↓reduceIte, List.length_cons, ih, Nat.add_comm]
    · simp only [cuts, done, changed, Bool.false_eq_true, ↓reduceIte, ih, Nat.zero_add]

end RotationBST.Combo.Rounds
