module

public import RotationBST.Algorithms.Combination.Worker.Rounds
public import RotationBST.Algorithms.Combination.Rounds.Cuts

@[expose] public section
namespace RotationBST.Combo.Worker

/-- The first switch recorded by the actual controller closes an operational
worker round on precisely the covered contiguous request segment. -/
theorem first_closed {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (boundary : Nat) (later : List Nat)
    (cut : Rounds.cuts worker budget restore s offset xs = boundary :: later) :
    ClosedRound worker s.side s.workerState s.left (xs.take (boundary - offset + 1)) := by
  induction xs generalizing s offset with
  | nil => simp [Rounds.cuts] at cut
  | cons x xs ih =>
    by_cases done : (Controller.serve worker budget restore s x).done = true
    · by_cases firstDone : (Controller.attempt worker s.side x s.left s.workerState).done = true
      · have next : Controller.serve worker budget restore s x =
            ⟨⟨s.side, (Controller.attempt worker s.side x s.left s.workerState).state,
              (Controller.attempt worker s.side x s.left s.workerState).left⟩, true, false,
              s.left - (Controller.attempt worker s.side x s.left s.workerState).left⟩ := by
          simp only [Controller.serve, firstDone, ↓reduceIte]
        have tailCut : Rounds.cuts worker budget restore (Controller.serve worker budget restore s x).state
            (offset + 1) xs = boundary :: later := by
          simpa only [Rounds.cuts, done, next, Bool.false_eq_true, ↓reduceIte] using cut
        have inside := (Rounds.cuts_ordered worker budget restore
          (Controller.serve worker budget restore s x).state (offset + 1) xs).2 boundary
          (by rw [tailCut]; exact List.mem_cons_self ..)
        have closed := ih _ (offset + 1) tailCut
        rw [next] at closed
        have delta : boundary - offset = boundary - (offset + 1) + 1 := by omega
        rw [List.take_succ_cons, delta]
        exact ClosedRound.cons (Controller.attempt_run worker s.side x s.left s.workerState) firstDone closed
      · have failed : (Controller.attempt worker s.side x s.left s.workerState).done = false := by
          cases h : (Controller.attempt worker s.side x s.left s.workerState).done <;> simp_all
        have switched : (Controller.serve worker budget restore s x).switched = true := by
          simp only [Controller.serve, failed, Bool.false_eq_true, ↓reduceIte]
        have cutEq : offset :: Rounds.cuts worker budget restore (Controller.serve worker budget restore s x).state
            (offset + 1) xs = boundary :: later := by
          simpa only [Rounds.cuts, done, switched, ↓reduceIte] using cut
        have same := (List.cons.inj cutEq).1
        rw [← same, Nat.sub_self]
        change ClosedRound worker s.side s.workerState s.left [x]
        exact .failed (Controller.attempt_run worker s.side x s.left s.workerState) failed
    · simp [Rounds.cuts, done] at cut

/-- Finishing the first closed round's request span on that same worker would
cost strictly more than the budget consumed before its interruption. -/
theorem first_lower_bound {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (offset : Nat) (xs : List Nat) (boundary : Nat) (later : List Nat)
    (cut : Rounds.cuts worker budget restore s offset xs = boundary :: later) (final : σ) (cost : Nat)
    (complete : Requests worker s.side s.workerState (xs.take (boundary - offset + 1)) final cost) :
    s.left < cost :=
  (first_closed worker budget restore s offset xs boundary later cut).lower_bound complete

end RotationBST.Combo.Worker
