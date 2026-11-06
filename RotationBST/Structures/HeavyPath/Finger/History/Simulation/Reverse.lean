module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

theorem source_append {α : Type} (c : Config α) (xs ys : List Multifinger.Opcode) :
    sourceRun c (xs ++ ys) = (sourceRun c xs).bind (fun next => sourceRun next ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append, sourceRun, ih, Option.bind_assoc]

/-- An inverse restores labels, the entire source tree, and its cursor. -/
theorem source_inverse {α : Type} {op : Multifinger.Opcode} {a b : Config α}
    (legal : perform op a = some b) : sourceRun b op.inverse = some a := by
  unfold perform at legal
  split at legal <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst b; rfl

/-- A legal source stream can be reversed with at most three instructions per
original instruction, using the same six-operation source language. -/
theorem source_restore {α : Type} {ops : List Multifinger.Opcode} {a b : Config α}
    (legal : sourceRun a ops = some b) : sourceRun b (Multifinger.undo ops) = some a := by
  induction ops generalizing a with
  | nil => simp only [sourceRun, Option.some.injEq] at legal; subst b; rfl
  | cons op ops ih =>
    cases first : perform op a with
    | none => simp only [sourceRun, first, Option.bind_none, reduceCtorEq] at legal
    | some c =>
      have rest : sourceRun c ops = some b := by
        simpa only [sourceRun, first, Option.bind_some] using legal
      rw [Multifinger.undo_cons, source_append, ih rest, Option.bind_some]
      exact source_inverse first

end RotationBST.HeavyPath.Finger.History.Simulation
