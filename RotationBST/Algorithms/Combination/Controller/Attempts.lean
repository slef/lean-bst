module

public import RotationBST.Algorithms.Combination.Controller.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Controller

theorem attempt_left {σ : Type} (worker : Worker σ) (side : Bool) (x fuel : Nat) (s : σ) :
    (attempt worker side x fuel s).left ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [attempt]
  | succ fuel ih =>
    simp only [attempt]
    split
    · simp
    · exact le_trans (ih _) (Nat.le_succ _)

/-- The executable attempt performs precisely its consumed budget. -/
theorem attempt_run {σ : Type} (worker : Worker σ) (side : Bool) (x fuel : Nat) (s : σ) :
    AttemptRun worker side x fuel s (attempt worker side x fuel s)
      (fuel - (attempt worker side x fuel s).left) := by
  induction fuel generalizing s with
  | zero => exact .exhausted
  | succ fuel ih =>
    rcases nextEq : worker.step side s x with ⟨t, done⟩
    cases done with
    | false =>
      simp only [attempt, nextEq, Bool.false_eq_true, ↓reduceIte]
      have bound := attempt_left worker side x fuel t
      convert AttemptRun.more nextEq (ih t) using 1; omega
    | true =>
      simpa only [attempt, nextEq, ↓reduceIte, Nat.add_sub_cancel_left] using
        (AttemptRun.done (fuel := fuel) nextEq)

/-- Every attempt preserves the exact sum of consumed and unused work. -/
theorem AttemptRun.account {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work) :
    work + result.left = fuel := by
  induction run with
  | exhausted => rfl
  | done => simp [Nat.add_comm]
  | more _ _ ih => omega

theorem AttemptRun.failed {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work)
    (failed : result.done = false) : result.left = 0 ∧ work = fuel := by
  induction run with
  | exhausted => exact ⟨rfl, rfl⟩
  | done => contradiction
  | more _ _ ih => obtain ⟨left, spent⟩ := ih failed; exact ⟨left, by omega⟩

theorem AttemptRun.positive {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work)
    (done : result.done = true) : 1 ≤ work := by
  cases run with
  | exhausted => contradiction
  | done => exact Nat.le_refl _
  | more => omega

/-- A successful attempt is unchanged by extra fuel, except for the unused
budget. The worker stops at the same first completion and has the same state. -/
theorem attempt_extra {σ : Type} (worker : Worker σ) (side : Bool) (x fuel extra : Nat) (s : σ)
    (done : (attempt worker side x fuel s).done = true) :
    attempt worker side x (fuel + extra) s =
      { attempt worker side x fuel s with left := (attempt worker side x fuel s).left + extra } := by
  induction fuel generalizing s with
  | zero => simp [attempt] at done
  | succ fuel ih =>
    rcases nextEq : worker.step side s x with ⟨t, finished⟩
    cases finished with
    | true => simp [attempt, nextEq, Nat.add_right_comm]
    | false =>
      simp only [attempt, nextEq, Bool.false_eq_true, ↓reduceIte] at done ⊢
      rw [Nat.succ_add]
      simpa only [attempt, nextEq, Bool.false_eq_true, ↓reduceIte] using ih t done

end RotationBST.Combo.Controller
