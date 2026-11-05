module

public import RotationBST.Models.Multifinger.Program.Definitions.Abstract
public import RotationBST.Models.Multifinger.Proofs
public import RotationBST.Models.Pointer.Location

@[expose] public section
namespace RotationBST.Multifinger

theorem perform_sound {op : Opcode} {a b : Pointer.Config} (result : perform op a = some b) :
    Pointer.Step a b := by
  unfold perform at result
  split at result <;> simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst b; constructor

theorem perform_complete {a b : Pointer.Config} (step : Pointer.Step a b) :
    ∃ op, perform op a = some b := by
  cases step with
  | downLeft => exact ⟨.downLeft, rfl⟩
  | downRight => exact ⟨.downRight, rfl⟩
  | upLeft => exact ⟨.upLeft, rfl⟩
  | upRight => exact ⟨.upRight, rfl⟩
  | rotateLeftChild => exact ⟨.rotateLeftChild, rfl⟩
  | rotateRightChild => exact ⟨.rotateRightChild, rfl⟩

theorem Command.Step.multifinger {fingers : Nat} {s t : State fingers} {cmd : Command fingers}
    (step : cmd.Step s t) : Multifinger.Step s cmd.finger t := by
  obtain ⟨a, b, x, tree, key, operation, touched, rfl⟩ := step
  exact .execute tree key (perform_sound operation) touched

/-- A command's target is determined by the current reference state alone. -/
theorem Command.Step.deterministic {fingers : Nat} {s t u : State fingers} {cmd : Command fingers}
    (left : cmd.Step s t) (right : cmd.Step s u) : t = u := by
  obtain ⟨a, b, x, treeA, keyA, operationA, touchedA, rfl⟩ := left
  obtain ⟨c, d, y, treeC, keyC, operationC, touchedC, rfl⟩ := right
  have cursor : a = c := Pointer.Config.ext_key (treeA.trans treeC.symm) keyA keyC
  subst c
  have same : b = d := Option.some.inj (operationA.symm.trans operationC)
  subst d
  have key : x = y := Option.some.inj (touchedA.symm.trans touchedC)
  subst y
  rfl

theorem step_command {fingers : Nat} {s t : State fingers} {i : Fin fingers} (step : Step s i t) :
    ∃ cmd : Command fingers, cmd.finger = i ∧ cmd.Step s t := by
  cases step with
  | execute tree key instruction touched =>
    obtain ⟨op, operation⟩ := perform_complete instruction
    exact ⟨⟨i, op⟩, rfl, _, _, _, tree, key, operation, touched, rfl⟩

theorem Program.trace {fingers : Nat} {s t : State fingers} {commands : List (Command fingers)} {touches : List Nat}
    (program : Program s commands touches t) : Trace s touches t := by
  induction program with
  | nil => exact .refl
  | cons step _ ih => exact .step step.multifinger ih

theorem Program.length {fingers : Nat} {s t : State fingers} {commands : List (Command fingers)} {touches : List Nat}
    (program : Program s commands touches t) : commands.length = touches.length := by
  induction program with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem trace_program {fingers : Nat} {s t : State fingers} {touches : List Nat} (trace : Trace s touches t) :
    ∃ commands, Program s commands touches t := by
  induction trace with
  | refl => exact ⟨[], .nil⟩
  | step step _ ih =>
    obtain ⟨cmd, eq, instruction⟩ := step_command step
    obtain ⟨commands, program⟩ := ih
    exact ⟨cmd :: commands, by simpa only [eq] using Program.cons instruction program⟩

end RotationBST.Multifinger
