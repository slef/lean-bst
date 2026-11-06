module

public import RotationBST.Algorithms.Combination.Controller.Progress

@[expose] public section
namespace RotationBST.Combo.Controller

/-- A completed trace agrees exactly with the executable prefix driver. -/
theorem Execution.computed {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) :
    run worker budget restore s xs = some (t, cost) := by
  induction execution with
  | nil => rfl
  | cons done _ ih => simp only [run, done, ↓reduceIte, ih, Option.map_some]

/-- For valid inputs the fresh-round bound makes the entire controller total.
Unused work stays in range, and each request needs at most two attempts. -/
theorem complete {σ : Type} (worker : Worker σ) (n bound budget restore : Nat)
    (bounded : FreshBound worker n bound) (enough : bound ≤ budget)
    (s : State σ) (limit : s.left ≤ budget) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ final cost switches, Execution worker budget restore s xs final cost switches ∧
      run worker budget restore s xs = some (final, cost) ∧ final.left ≤ budget ∧
      cost ≤ (2 * budget + restore) * xs.length := by
  induction xs generalizing s with
  | nil => exact ⟨s, 0, 0, .nil, rfl, limit, Nat.le_refl _⟩
  | cons x xs ih =>
    have done := serve_done worker n bound budget restore bounded enough s x (valid x (by simp))
    have nextLimit := serve_left worker budget restore s x limit
    obtain ⟨final, cost, switches, tail, computed, finalLimit, bound⟩ :=
      ih _ nextLimit (fun y member => valid y (List.mem_cons_of_mem _ member))
    have execution := Execution.cons done tail
    refine ⟨final, _, _, execution, execution.computed, finalLimit, ?_⟩
    have headBound := serve_work_bound worker budget restore s x limit
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- The accounting identity telescopes across all requests, including a switch
in the middle of one request and a fully consumed previous round. -/
theorem Execution.account {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) :
    cost + t.left = s.left + switches * (budget + restore) := by
  induction execution with
  | nil => simp
  | @cons s t x xs cost switches done tail ih =>
    have head := serve_account worker budget restore s x
    by_cases changed : (serve worker budget restore s x).switched = true
    · simp only [changed, ↓reduceIte, Nat.add_mul, Nat.one_mul] at head ⊢
      omega
    · simp only [changed, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] at head ⊢
      omega

/-- The controller cannot make more switches than completed requests. -/
theorem Execution.switches {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) : switches ≤ xs.length := by
  induction execution with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => simp only [List.length_cons]; split <;> omega

/-- Executing an input extension continues from exactly the prior state and
adds exactly its work. The already executed prefix never depends on the suffix. -/
theorem run_append {σ : Type} (worker : Worker σ) (budget restore : Nat) (s : State σ) (xs ys : List Nat) :
    run worker budget restore s (xs ++ ys) =
      (run worker budget restore s xs).bind fun first =>
        (run worker budget restore first.1 ys).map fun last => (last.1, first.2 + last.2) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons x xs ih =>
    simp only [List.cons_append, run]
    by_cases done : (serve worker budget restore s x).done = true
    · simp only [done, ↓reduceIte, ih]
      cases resultEq : run worker budget restore (serve worker budget restore s x).state xs with
      | none => rfl
      | some result =>
        simp only [Option.bind_some, Option.map_some]
        cases run worker budget restore result.1 ys <;> simp [Nat.add_assoc]
    · simp only [done, Bool.false_eq_true, ↓reduceIte, Option.bind_none]

end RotationBST.Combo.Controller
