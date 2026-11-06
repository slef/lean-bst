module

public import RotationBST.Algorithms.Combination.Worker.Attempts

@[expose] public section
namespace RotationBST.Combo.Worker

theorem Requests.append {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t u : σ} {before after : Nat} {earlier later : List Nat}
    (first : Requests worker side s earlier t before) (second : Requests worker side t later u after) :
    Requests worker side s (earlier ++ later) u (before + after) := by
  induction first with
  | nil => simpa only [List.nil_append, Nat.zero_add] using second
  | cons access _ ih => simpa only [List.cons_append, Nat.add_assoc] using Requests.cons access (ih second)

theorem Requests.unique {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t u : σ} {cost otherCost : Nat} {xs : List Nat}
    (first : Requests worker side s xs t cost) (second : Requests worker side s xs u otherCost) :
    t = u ∧ cost = otherCost := by
  induction first generalizing u otherCost with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons access tail ih =>
    cases second with
    | cons other rest =>
      obtain ⟨sameState, sameCost⟩ := Controller.AttemptRun.completed_unique access rfl other rfl
      dsimp only at sameState sameCost
      subst_vars
      obtain ⟨state, cost⟩ := ih rest
      exact ⟨state, by omega⟩

theorem Requests.length_le_cost {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {cost : Nat} {xs : List Nat} (run : Requests worker side s xs t cost) : xs.length ≤ cost := by
  induction run with
  | nil => exact Nat.le_refl _
  | cons access _ ih =>
    have positive := Controller.AttemptRun.positive access rfl
    simp only [List.length_cons]
    omega

/-- The exhausted round's entire budget is strictly below the cost of
completing its covered request segment on the same deterministic worker. -/
theorem ClosedRound.lower_bound {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {budget cost : Nat} {xs : List Nat}
    (round : ClosedRound worker side s budget xs) (complete : Requests worker side s xs t cost) :
    budget < cost := by
  induction round generalizing t cost with
  | failed attempt failed =>
    cases complete with
    | cons access tail =>
      cases tail
      have bound := attempt.failed_lt_complete failed access rfl
      simpa only [Nat.add_zero] using bound
  | cons attempt done tail ih =>
    cases complete with
    | cons access rest =>
      obtain ⟨sameState, sameCost⟩ := attempt.completed_unique done access rfl
      have smaller := ih (by simpa only [sameState] using rest)
      have account := attempt.account
      omega

/-- A completed prefix can be reattached to a later exhausted attempt. This
keeps the original round's start state and charges its entire budget. -/
theorem ClosedRound.prepend {σ : Type} {worker : Controller.Worker σ} {side : Bool}
    {s t : σ} {before remaining : Nat} {earlier suffix : List Nat}
    (complete : Requests worker side s earlier t before) (round : ClosedRound worker side t remaining suffix) :
    ClosedRound worker side s (before + remaining) (earlier ++ suffix) := by
  induction complete with
  | nil => simpa only [Nat.zero_add, List.nil_append] using round
  | @cons s t u x xs cost rest access tail ih =>
    have run := Controller.attempt_run worker side x (cost + (rest + remaining)) s
    have base : Controller.attempt worker side x cost s = ⟨t, 0, true⟩ :=
      Controller.AttemptRun.computed access
    have extra := Controller.attempt_extra worker side x cost (rest + remaining) s (by rw [base])
    rw [base] at extra
    simp only [Nat.zero_add] at extra
    rw [extra] at run
    have continued := ClosedRound.cons run rfl (ih round)
    simpa only [List.cons_append, Nat.add_assoc] using continued

end RotationBST.Combo.Worker
