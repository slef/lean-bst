module

public import RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Attempts
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Pair
open Controller

/-- Exact transport includes interrupted attempts and their unused fuel. -/
theorem attempt_map {α β : Type} (source : Controller.Worker α) (target : Controller.Worker β)
    (sourceSide targetSide : Bool) (embed : α → β)
    (commutes : ∀ s x, target.step targetSide (embed s) x =
      (embed (source.step sourceSide s x).1, (source.step sourceSide s x).2))
    (x fuel : Nat) (s : α) :
    Controller.attempt target targetSide x fuel (embed s) =
      let result := Controller.attempt source sourceSide x fuel s
      ⟨embed result.state, result.left, result.done⟩ := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [Controller.attempt, commutes]
    split
    · rfl
    · exact ih _

theorem access_map {α β : Type} {source : Controller.Worker α} {target : Controller.Worker β}
    {sourceSide targetSide : Bool} (embed : α → β)
    (commutes : ∀ s x, target.step targetSide (embed s) x =
      (embed (source.step sourceSide s x).1, (source.step sourceSide s x).2))
    {s t : α} {x cost : Nat} (run : Worker.Access source sourceSide s x t cost) :
    Worker.Access target targetSide (embed s) x (embed t) cost := by
  have computed := attempt_map source target sourceSide targetSide embed commutes x cost s
  rw [run.computed] at computed
  have ran := Controller.attempt_run target targetSide x cost (embed s)
  simpa only [computed, Nat.sub_zero, Worker.Access] using ran

theorem access_pullback {α β : Type} {source : Controller.Worker α} {target : Controller.Worker β}
    {sourceSide targetSide : Bool} (embed : α → β)
    (commutes : ∀ s x, target.step targetSide (embed s) x =
      (embed (source.step sourceSide s x).1, (source.step sourceSide s x).2))
    {s : α} {t : β} {x cost : Nat} (run : Worker.Access target targetSide (embed s) x t cost) :
    ∃ next, t = embed next ∧ Worker.Access source sourceSide s x next cost := by
  have computed := (attempt_map source target sourceSide targetSide embed commutes x cost s).symm.trans run.computed
  have same := congrArg Controller.Attempt.state computed
  have left := congrArg Controller.Attempt.left computed
  have done := congrArg Controller.Attempt.done computed
  change (Controller.attempt source sourceSide x cost s).left = 0 at left
  have ran := Controller.attempt_run source sourceSide x cost s
  refine ⟨_, same.symm, ?_⟩
  have completed := ran.to_access done
  simpa only [left, Nat.sub_zero] using completed

theorem requests_map {α β : Type} {source : Controller.Worker α} {target : Controller.Worker β}
    {sourceSide targetSide : Bool} (embed : α → β)
    (commutes : ∀ s x, target.step targetSide (embed s) x =
      (embed (source.step sourceSide s x).1, (source.step sourceSide s x).2))
    {s t : α} {xs : List Nat} {cost : Nat} (run : Worker.Requests source sourceSide s xs t cost) :
    Worker.Requests target targetSide (embed s) xs (embed t) cost := by
  induction run with
  | nil => exact .nil
  | cons first rest ih => exact .cons (access_map embed commutes first) ih

theorem requests_pullback {α β : Type} {source : Controller.Worker α} {target : Controller.Worker β}
    {sourceSide targetSide : Bool} (embed : α → β)
    (commutes : ∀ s x, target.step targetSide (embed s) x =
      (embed (source.step sourceSide s x).1, (source.step sourceSide s x).2))
    {s : α} {t : β} {xs : List Nat} {cost : Nat} (run : Worker.Requests target targetSide (embed s) xs t cost) :
    ∃ next, t = embed next ∧ Worker.Requests source sourceSide s xs next cost := by
  generalize initial : embed s = start at run
  induction run generalizing s with
  | nil => exact ⟨s, initial.symm, .nil⟩
  | cons first rest ih =>
    rw [← initial] at first
    obtain ⟨middle, rfl, head⟩ := access_pullback embed commutes first
    obtain ⟨last, same, tail⟩ := ih rfl
    exact ⟨last, same, .cons head tail⟩

end RotationBST.Combo.Worker.Pair
