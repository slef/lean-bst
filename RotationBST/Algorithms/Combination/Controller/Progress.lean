module

public import RotationBST.Algorithms.Combination.Controller.Attempts

@[expose] public section
namespace RotationBST.Combo.Controller

theorem FreshBound.mono {σ : Type} {worker : Worker σ} {n bound budget : Nat}
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget) : FreshBound worker n budget := by
  intro side x valid
  have extra := attempt_extra worker side x bound (budget - bound) (worker.restart side) (bounded side x valid)
  rw [Nat.add_sub_of_le enough] at extra
  rw [extra]
  exact bounded side x valid

/-- The controller's output is backed by exactly one successful attempt, or
an exhausted attempt followed by the explicitly charged restart and retry. -/
theorem serve_service {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    Service worker budget restore s x (serve worker budget restore s x) := by
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  all_goals simp only [serve, firstDone, Bool.false_eq_true, ↓reduceIte]
  · exact .finish (attempt_run worker s.side x s.left s.workerState) firstDone
  · exact .switch (attempt_run worker s.side x s.left s.workerState)
      (by cases h : (attempt worker s.side x s.left s.workerState).done <;> simp_all) (attempt_run worker (!s.side) x budget (worker.restart (!s.side)))

/-- A retry from the fixed initial state must finish within the fresh budget.
Consequently no request can trigger two switches. -/
theorem serve_done {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget) (s : State σ) (x : Nat) (valid : x < n) :
    (serve worker budget restore s x).done = true := by
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  · simp only [serve, firstDone, ↓reduceIte]
  · simpa only [serve, firstDone, Bool.false_eq_true, ↓reduceIte] using bounded.mono enough (!s.side) x valid

theorem serve_left {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat)
    (limit : s.left ≤ budget) : (serve worker budget restore s x).state.left ≤ budget := by
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  all_goals simp only [serve, firstDone, Bool.false_eq_true, ↓reduceIte]
  · exact Nat.le_trans (attempt_left worker s.side x s.left s.workerState) limit
  · exact attempt_left worker (!s.side) x budget (worker.restart (!s.side))

/-- Exact budget accounting includes the unused suffix of the new round when
there is a switch. A failed first attempt has no unused work. -/
theorem serve_account {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    (serve worker budget restore s x).work + (serve worker budget restore s x).state.left =
      s.left + if (serve worker budget restore s x).switched then restore + budget else 0 := by
  have first := attempt_run worker s.side x s.left s.workerState
  have second := attempt_run worker (!s.side) x budget (worker.restart (!s.side))
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  all_goals simp only [serve, firstDone, Bool.false_eq_true, ↓reduceIte]
  · have account := first.account
    simpa only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using account
  · have failed := first.failed (by cases h : (attempt worker s.side x s.left s.workerState).done <;> simp_all)
    have account := second.account
    omega

theorem serve_alternates {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat) :
    (serve worker budget restore s x).state.side =
      if (serve worker budget restore s x).switched then !s.side else s.side := by
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  all_goals simp only [serve, firstDone, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl

theorem serve_work_bound {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (x : Nat)
    (limit : s.left ≤ budget) : (serve worker budget restore s x).work ≤ 2 * budget + restore := by
  by_cases firstDone : (attempt worker s.side x s.left s.workerState).done = true
  all_goals simp only [serve, firstDone, Bool.false_eq_true, ↓reduceIte]
  all_goals omega

/-- Every new round completes its first request within its budget.
In particular, the same unfinished request cannot reappear in a later round
of the same worker. -/
theorem fresh_completes {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget) (side : Bool) (x : Nat) (valid : x < n) :
    (serve worker budget restore ⟨side, worker.restart side, budget⟩ x).switched = false ∧
      (serve worker budget restore ⟨side, worker.restart side, budget⟩ x).work ≤ bound := by
  have done := bounded.mono enough side x valid
  have extra := attempt_extra worker side x bound (budget - bound) (worker.restart side) (bounded side x valid)
  rw [Nat.add_sub_of_le enough] at extra
  simp only [serve, done, ↓reduceIte]
  constructor
  · trivial
  · rw [extra]
    dsimp
    omega

end RotationBST.Combo.Controller
