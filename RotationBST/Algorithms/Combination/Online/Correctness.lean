module

public import RotationBST.Algorithms.Combination.Online.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Combo.Online

variable {σ : Type} {worker : Controller.Worker σ} {saved : Tree}
  {model : Refinement.WorkerModel worker saved} {data : Nat → Nat} {budget restore : Nat}

theorem advance_spec (contract : Contract model data budget restore) (s : State model data budget)
    (x : Nat) (valid : x < saved.size) : Transition restore s x (advance contract s x) := by
  rw [advance, dite_eq_left valid]
  exact Classical.choose_spec (advance_exists contract s x valid)

/-- Exact prefix composition, including the physical state and charged cost.
Appending future requests cannot change any earlier implementation choice. -/
theorem run_append (contract : Contract model data budget restore) (s : State model data budget) (xs ys : List Nat) :
    run contract s (xs ++ ys) =
      let first := run contract s xs
      let rest := run contract first.1 ys
      (rest.1, first.2 + rest.2) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih => simp only [List.cons_append, run, ih, Nat.add_assoc]

/-- The chosen physical requests refine the same logical controller run;
the hand potential telescopes through every request boundary. -/
theorem run_spec (contract : Contract model data budget restore) (s : State model data budget)
    (xs : List Nat) (valid : ∀ x ∈ xs, x < saved.size) :
    ∃ work switches,
      Controller.Execution worker budget restore s.controller xs (run contract s xs).1.controller work switches ∧
      Pointer.Execution s.hand.tree xs (run contract s xs).1.hand.tree (run contract s xs).2 ∧
      (run contract s xs).2 + (run contract s xs).1.hand.potential ≤ 8384 * work + s.hand.potential := by
  induction xs generalizing s with
  | nil => exact ⟨0, 0, .nil, .nil, by simp [run]⟩
  | cons x xs ih =>
    have first := advance_spec contract s x (valid x (by simp))
    obtain ⟨work, switches, logical, physical, bound⟩ := ih (advance contract s x).1
      (fun y member => valid y (List.mem_cons_of_mem x member))
    have tail : Controller.Execution worker budget restore
        (Controller.serve worker budget restore s.controller x).state xs
        (run contract (advance contract s x).1 xs).1.controller work switches := by
      simpa only [first.1] using logical
    refine ⟨_, _, Controller.Execution.cons (completes contract s x (valid x (by simp))) tail,
      Pointer.Execution.cons first.2.1 physical, ?_⟩
    have charged := first.2.2.1
    simp only [run, Nat.mul_add] at bound ⊢
    omega

end RotationBST.Combo.Online
