module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Policy
public import RotationBST.Structures.HeavyPath.Finger.History.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

/-- Exact prefix composition, for any policy, including failure behavior. -/
theorem run_append {α : Type} (p : Policy α) (c : Config α) (s : State α)
    (xs ys : List Multifinger.Opcode) :
    run p c s (xs ++ ys) = (run p c s xs).bind fun first =>
      (run p first.source first.state ys).map fun last =>
        ⟨last.source, last.state, first.instructions ++ last.instructions⟩ := by
  induction xs generalizing c s with
  | nil => simp [run]
  | cons op ops ih =>
    simp only [List.cons_append, run]
    cases eq : p c s op with
    | none => rfl
    | some first =>
      simp only [Option.bind_some, ih]
      cases rest : run p first.source first.state ops with
      | none => rfl
      | some middle =>
        simp only [Option.bind_some, Option.map_some]
        cases last : run p middle.source middle.state ys <;> simp [List.append_assoc]

/-- Extending a successful input preserves the exact emitted physical prefix. -/
theorem run_prefix {α : Type} (p : Policy α) (c : Config α) (s : State α)
    (xs ys : List Multifinger.Opcode) {out : Output α}
    (completed : run p c s (xs ++ ys) = some out) :
    ∃ first, run p c s xs = some first ∧ first.instructions <+: out.instructions := by
  rw [run_append] at completed
  cases firstEq : run p c s xs with
  | none => simp [firstEq] at completed
  | some first =>
    simp only [firstEq, Option.bind_some] at completed
    cases lastEq : run p first.source first.state ys with
    | none => simp [lastEq] at completed
    | some last =>
      simp only [lastEq, Option.map_some, Option.some.injEq] at completed
      subst out
      exact ⟨first, rfl, ⟨last.instructions, rfl⟩⟩

/-- Every legal finite stream has a single physical trace and a telescoping
potential bound. The same policy is used for every stream and prefix. -/
theorem run_spec {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : sourceRun c ops = some final) :
    ∃ out, run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential := by
  induction ops generalizing c s with
  | nil =>
    simp only [sourceRun, Option.some.injEq] at legal
    exact ⟨⟨c, s, []⟩, rfl, legal, valid, rfl, by simp [Output.cost]⟩
  | cons op ops ih =>
    cases eq : perform op c with
    | none => simp [sourceRun, eq] at legal
    | some next =>
      have localSpec := policyValid c s op valid
      rw [eq] at localSpec
      obtain ⟨first, firstEq, sourceEq, firstValid, firstTrace, firstBound⟩ := localSpec
      have remaining : sourceRun first.source ops = some final := by
        simpa only [sourceRun, eq, Option.bind_some, sourceEq] using legal
      obtain ⟨last, lastEq, finalEq, lastValid, lastTrace, lastBound⟩ := ih firstValid remaining
      refine ⟨⟨last.source, last.state, first.instructions ++ last.instructions⟩, ?_, finalEq,
        lastValid, ?_, ?_⟩
      · simp only [run, firstEq, Option.bind_some, lastEq, Option.map_some]
      · simpa only [Multifinger.replay_append, firstTrace, Option.bind_some] using lastTrace
      · simp only [Output.cost, List.length_append, List.length_cons] at *
        omega

/-- A certified policy rejects exactly the illegal source streams. -/
theorem run_none_iff {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (ops : List Multifinger.Opcode) :
    run p c s ops = none ↔ sourceRun c ops = none := by
  induction ops generalizing c s with
  | nil => simp [run, sourceRun]
  | cons op ops ih =>
    have localSpec := policyValid c s op valid
    cases eq : perform op c with
    | none =>
      rw [eq] at localSpec
      simp [run, sourceRun, localSpec, eq]
    | some next =>
      rw [eq] at localSpec
      obtain ⟨first, firstEq, sourceEq, firstValid, _, _⟩ := localSpec
      simpa only [run, sourceRun, firstEq, eq, Option.bind_some, Option.map_eq_none_iff,
        sourceEq] using ih firstValid

/-- A fixed online instruction policy, starting at the original source tree,
has linear startup and constant amortized physical work per source instruction. -/
theorem initialized_run {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (start : State α) (startupCost : Nat),
      ConfigValid weight ⟨.node left key right, cs⟩ start ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨start.pair.tree, []⟩ startupCost ∧
      startupCost + start.potential ≤ 39 * (plug cs (.node left key right)).erase.size ∧
      ∀ (ops : List Multifinger.Opcode) (final : Config α),
        sourceRun ⟨.node left key right, cs⟩ ops = some final →
        ∃ out, run p ⟨.node left key right, cs⟩ start ops = some out ∧ out.source = final ∧
          ConfigValid weight out.source out.state ∧
          Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩
            ⟨out.state.pair.tree, []⟩ (startupCost + out.cost) ∧
          startupCost + out.cost + out.state.potential ≤
            39 * (plug cs (.node left key right)).erase.size + 62 * ops.length := by
  obtain ⟨start, startupCost, valid, trace, _, _, bound⟩ :=
    History.Results.state_initialization_bounded positive
  refine ⟨start, startupCost, valid, trace, bound, ?_⟩
  intro ops final legal
  obtain ⟨out, runEq, sourceEq, preserved, executed, amortized⟩ :=
    run_spec policyValid (c := ⟨.node left key right, cs⟩) valid legal
  exact ⟨out, runEq, sourceEq, preserved, trace.append (Multifinger.Replay.Results.physical executed), by omega⟩

end RotationBST.HeavyPath.Finger.History.Simulation
