module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Reverse
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Execution
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Minimum
open LabelledCursor

theorem potential_le {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : potential weight c ≤ s.potential :=
  Nat.sInf_le ⟨s, valid, rfl⟩

theorem attained {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) :
    ∃ best, ConfigValid weight c best ∧ best.potential = potential weight c :=
  Nat.sInf_mem (s := {n | ∃ best : State α, ConfigValid weight c best ∧ best.potential = n})
    ⟨s.potential, s, valid, rfl⟩

theorem excess_add {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : excess weight c s + potential weight c = s.potential :=
  Nat.sub_add_cancel (potential_le valid)

/-- Reverse simulation bounds how far the minimum representation credit can
fall along a source stream. The reverse stream is used only in the proof. -/
theorem potential_drop {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} (finalValid : ConfigValid weight final s)
    (legal : sourceRun c ops = some final) :
    potential weight c ≤ 186 * ops.length + potential weight final := by
  obtain ⟨best, bestValid, bestMinimum⟩ := attained finalValid
  obtain ⟨out, _, sourceEq, outValid, _, work⟩ :=
    run_spec policyValid bestValid (source_restore legal)
  have lower := potential_le outValid
  have inverseSize := Multifinger.Replay.Results.inverse_size ops
  rw [sourceEq] at lower
  omega

/-- The same physical execution has constant amortized cost with respect to
excess credit; no change to the causal policy or its instructions is needed. -/
theorem run_excess {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {out : Output α} (valid : ConfigValid weight c s)
    (legal : sourceRun c ops = some final) (completed : run p c s ops = some out) :
    out.cost + excess weight out.source out.state ≤ 248 * ops.length + excess weight c s := by
  obtain ⟨actual, actualRun, sourceEq, outValid, _, work⟩ := run_spec policyValid valid legal
  have same : actual = out := Option.some.inj (actualRun.symm.trans completed)
  subst actual
  have drop := potential_drop policyValid (sourceEq ▸ outValid) legal
  have initial := excess_add valid
  have finalCredit := excess_add outValid
  rw [← sourceEq] at drop
  omega

end RotationBST.HeavyPath.Finger.History.Simulation.Minimum
