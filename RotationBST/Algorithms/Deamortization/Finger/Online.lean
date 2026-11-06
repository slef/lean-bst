module

public import RotationBST.Algorithms.Deamortization.Finger.Preparation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

theorem prepare_append {α : Type} (p : Simulation.Policy α) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) (c : LabelledCursor.Config α) (s : State α) (xs ys : List Nat) :
    prepare p a past c s (xs ++ ys) = (prepare p a past c s xs).bind fun first =>
      (prepare p a (past ++ xs) first.source first.history ys).map fun last =>
        ⟨last.source, last.history, first.requests ++ last.requests⟩ := by
  induction xs generalizing past c s with
  | nil => simp [prepare]
  | cons key keys ih =>
    simp only [List.cons_append, prepare]
    cases firstEq : Simulation.run p c s (a.step past c key).1 with
    | none => rfl
    | some first =>
      simp only [Option.bind_some, ih, List.append_assoc]
      cases middleEq : prepare p a (past ++ [key]) first.source first.state keys with
      | none => rfl
      | some middle =>
        simp only [Option.bind_some, Option.map_some]
        cases lastEq : prepare p a (past ++ key :: keys) middle.source middle.history ys <;>
          simp [lastEq]

theorem prepare_prefix {α : Type} (p : Simulation.Policy α) (a : Simulation.Requests.Algorithm α)
    (past : List Nat) (c : LabelledCursor.Config α) (s : State α) (xs ys : List Nat)
    {out : PreparedOutput α} (completed : prepare p a past c s (xs ++ ys) = some out) :
    ∃ first, prepare p a past c s xs = some first ∧ first.requests <+: out.requests := by
  rw [prepare_append] at completed
  cases firstEq : prepare p a past c s xs with
  | none => simp [firstEq] at completed
  | some first =>
    simp only [firstEq, Option.bind_some] at completed
    cases lastEq : prepare p a (past ++ xs) first.source first.history ys with
    | none => simp [lastEq] at completed
    | some last =>
      simp only [lastEq, Option.map_some, Option.some.injEq] at completed
      subst out
      exact ⟨first, rfl, ⟨last.requests, rfl⟩⟩

/-- The complete transformation preserves literal emitted prefixes and the
per-request charge list when future user requests are appended. -/
theorem transform_prefix {α : Type} (sourcePolicy : Simulation.Policy α) (scheduler : Scheduler.Policy)
    (a : Simulation.Requests.Algorithm α) (past : List Nat) (c : LabelledCursor.Config α)
    (s : State α) (xs ys : List Nat) {out : Scheduler.Output}
    (completed : transform sourcePolicy scheduler a past c s (xs ++ ys) = some out) :
    ∃ first, transform sourcePolicy scheduler a past c s xs = some first ∧
      first.instructions <+: out.instructions ∧ first.costs <+: out.costs := by
  unfold transform at completed
  cases preparedEq : prepare sourcePolicy a past c s (xs ++ ys) with
  | none => simp [preparedEq] at completed
  | some prepared =>
    simp only [preparedEq, Option.bind_some] at completed
    obtain ⟨firstPrepared, firstEq, tail, listEq⟩ := prepare_prefix sourcePolicy a past c s xs ys preparedEq
    rw [← listEq] at completed
    obtain ⟨first, firstRun, codePrefix, costPrefix⟩ :=
      Scheduler.run_prefix scheduler (Scheduler.initial ⟨s.pair.tree, []⟩) firstPrepared.requests tail completed
    refine ⟨first, ?_, codePrefix, costPrefix⟩
    simpa only [transform, firstEq, Option.bind_some] using firstRun

end RotationBST.Deamortization.Finger
