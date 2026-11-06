module

public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Proofs
public import RotationBST.Models.Pointer.Traces
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Multifinger

theorem replay_append (first last : List Opcode) (cursor : Pointer.Config) :
    replay (first ++ last) cursor = (replay first cursor).bind (replay last) := by
  induction first generalizing cursor with
  | nil => rfl
  | cons op ops ih => simp only [List.cons_append, replay, ih, Option.bind_assoc]

/-- The log length is exactly the number of charged physical instructions. -/
theorem replay_trace {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    Pointer.Trace a b ops.length := by
  induction ops generalizing a with
  | nil => simp only [replay, Option.some.injEq] at run; subst b; exact .refl
  | cons op ops ih =>
    cases first : perform op a with
    | none => simp only [replay, first, Option.bind_none, reduceCtorEq] at run
    | some c =>
      have rest : replay ops c = some b := by simpa only [replay, first, Option.bind_some] using run
      exact .step (perform_sound first) (ih rest)

/-- Every existing physical trace has a recorded instruction stream of exactly
the same length. This is a correspondence theorem, not a logging-cost claim. -/
theorem trace_replay {a b : Pointer.Config} {k : Nat} (trace : Pointer.Trace a b k) :
    ∃ ops, ops.length = k ∧ replay ops a = some b := by
  induction trace with
  | refl => exact ⟨[], rfl, rfl⟩
  | step step _ ih =>
    obtain ⟨op, first⟩ := perform_complete step
    obtain ⟨ops, length, rest⟩ := ih
    exact ⟨op :: ops, by simp only [List.length_cons, length], by simp only [replay, first, Option.bind_some, rest]⟩

theorem inverse_replay {op : Opcode} {a b : Pointer.Config} (run : perform op a = some b) :
    replay op.inverse b = some a := by
  unfold perform at run
  split at run <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst b; rfl

theorem undo_cons (op : Opcode) (ops : List Opcode) : undo (op :: ops) = undo ops ++ op.inverse := by
  simp [undo, List.flatMap_append]

theorem undo_replay {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    replay (undo ops) b = some a := by
  induction ops generalizing a with
  | nil => simp only [replay, Option.some.injEq] at run; subst b; rfl
  | cons op ops ih =>
    cases first : perform op a with
    | none => simp only [replay, first, Option.bind_none, reduceCtorEq] at run
    | some c =>
      have rest : replay ops c = some b := by simpa only [replay, first, Option.bind_some] using run
      rw [undo_cons, replay_append, ih rest, Option.bind_some]
      exact inverse_replay first

theorem inverse_length (op : Opcode) : op.inverse.length ≤ 3 := by cases op <;> decide

theorem undo_length (ops : List Opcode) : (undo ops).length ≤ 3 * ops.length := by
  induction ops with
  | nil => simp [undo]
  | cons op ops ih =>
    rw [undo_cons, List.length_append, List.length_cons]
    have bound := inverse_length op
    omega

/-- A successful log restores its exact starting cursor, including context. -/
theorem replay_roundtrip {ops : List Opcode} {a b : Pointer.Config} (run : replay ops a = some b) :
    replay (ops ++ undo ops) a = some a := by
  rw [replay_append, run, Option.bind_some]
  exact undo_replay run

end RotationBST.Multifinger
