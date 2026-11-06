module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Visit
public import RotationBST.Models.Pointer.Reshape
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

/-- The source algorithm's output composes without future requests. -/
theorem source_requests_append {α : Type} (a : Algorithm α) (past : List Nat) (c : Config α)
    (xs ys : List Nat) :
    a.runFrom past c (xs ++ ys) =
      let first := a.runFrom past c xs
      let last := a.runFrom (past ++ xs) first.2 ys
      (first.1 ++ last.1, last.2) := by
  induction xs generalizing past c with
  | nil => simp [Algorithm.runFrom]
  | cons x xs ih => simp only [List.cons_append, Algorithm.runFrom, ih, List.append_assoc, List.nil_append]

/-- Exact request-prefix composition of the emitted physical code. -/
theorem run_append {α : Type} (p : Policy α) (a : Algorithm α) (past : List Nat)
    (c : Config α) (s : State α) (xs ys : List Nat) :
    run p a past c s (xs ++ ys) = (run p a past c s xs).bind fun first =>
      (run p a (past ++ xs) first.source first.state ys).map fun last =>
        ⟨last.source, last.state, first.instructions ++ last.instructions⟩ := by
  induction xs generalizing past c s with
  | nil => simp [run]
  | cons key keys ih =>
    simp only [List.cons_append, run]
    cases eq : Simulation.run p c s (a.step past c key).1 with
    | none => rfl
    | some first =>
      simp only [Option.bind_some, ih, List.append_assoc]
      cases rest : run p a (past ++ [key]) first.source first.state keys with
      | none => rfl
      | some middle =>
        simp only [Option.bind_some, Option.map_some]
        cases last : run p a (past ++ key :: keys) middle.source middle.state ys <;>
          simp [List.append_assoc, last]

/-- Every prefix of requests retains exactly the physical output already sent. -/
theorem run_prefix {α : Type} (p : Policy α) (a : Algorithm α) (past : List Nat)
    (c : Config α) (s : State α) (xs ys : List Nat) {out : Output α}
    (completed : run p a past c s (xs ++ ys) = some out) :
    ∃ first, run p a past c s xs = some first ∧ first.instructions <+: out.instructions := by
  rw [run_append] at completed
  cases firstEq : run p a past c s xs with
  | none => simp [firstEq] at completed
  | some first =>
    simp only [firstEq, Option.bind_some] at completed
    cases lastEq : run p a (past ++ xs) first.source first.state ys with
    | none => simp [lastEq] at completed
    | some last =>
      simp only [lastEq, Option.map_some, Option.some.injEq] at completed
      subst out
      exact ⟨first, rfl, ⟨last.instructions, rfl⟩⟩

/-- Request-level simulation of any source algorithm. The cost convention
charges each request once and every emitted physical opcode once. -/
theorem run_spec {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, run p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      Pointer.Execution s.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
      out.cost + out.state.potential ≤ 62 * (a.runFrom past c keys).1.length + s.potential := by
  induction keys generalizing past c s with
  | nil => exact ⟨⟨c, s, []⟩, rfl, rfl, valid, rfl, .nil, by simp [Output.cost, Algorithm.runFrom]⟩
  | cons key keys ih =>
    have sourceSearch := a.correct past c key (config_nonempty valid) (validKeys key (by simp))
    obtain ⟨first, firstRun, firstEq, firstValid, firstReplay, firstBound, firstServes⟩ :=
      serves policyValid valid sourceSearch
    have sizeEq : c.tree.erase.size = first.source.tree.erase.size := by
      rw [firstEq]
      exact source_size sourceSearch.legal
    have restValid : ∀ x ∈ keys, x < first.source.tree.erase.size := by
      intro x hx
      rw [← sizeEq]
      exact validKeys x (by simp [hx])
    obtain ⟨last, lastRun, lastEq, lastValid, lastReplay, lastExecution, lastBound⟩ :=
      ih (past ++ [key]) firstValid restValid
    refine ⟨⟨last.source, last.state, first.instructions ++ last.instructions⟩, ?_, ?_, lastValid, ?_, ?_, ?_⟩
    · simp only [run, firstRun, Option.bind_some, lastRun, Option.map_some]
    · simpa only [Algorithm.runFrom, firstEq] using lastEq
    · simpa only [Multifinger.replay_append, firstReplay, Option.bind_some] using lastReplay
    · convert Pointer.Execution.cons firstServes lastExecution using 1
      simp only [Output.cost, List.length_append, List.length_cons]
      omega
    · rw [firstEq] at lastBound
      simp only [Algorithm.runFrom, Output.cost, List.length_append] at *
      omega

/-- The complete request comparison, with one initialized state chosen before
all past histories and future request sequences. -/
theorem initialized_run {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (start : State α) (startupCost : Nat),
      ConfigValid weight ⟨.node left key right, cs⟩ start ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨start.pair.tree, []⟩ startupCost ∧
      startupCost + start.potential ≤ 39 * (plug cs (.node left key right)).erase.size ∧
      ∀ (past keys : List Nat),
        (∀ x ∈ keys, x < (plug cs (.node left key right)).erase.size) →
        ∃ out, run p a past ⟨.node left key right, cs⟩ start keys = some out ∧
          out.source = (a.runFrom past ⟨.node left key right, cs⟩ keys).2 ∧
          ConfigValid weight out.source out.state ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          (keys ≠ [] → Pointer.Execution (plug cs (.node left key right)).erase keys
            out.state.pair.tree (startupCost + (keys.length + out.cost))) ∧
          startupCost + keys.length + out.cost + out.state.potential ≤
            39 * (plug cs (.node left key right)).erase.size +
              62 * (keys.length + (a.runFrom past ⟨.node left key right, cs⟩ keys).1.length) := by
  obtain ⟨start, startupCost, valid, trace, _, _, bound⟩ :=
    History.Results.state_initialization_bounded positive
  refine ⟨start, startupCost, valid, trace, bound, ?_⟩
  intro past keys validKeys
  obtain ⟨out, completed, sourceEq, preserved, _, executed, amortized⟩ :=
    run_spec policyValid a past (c := ⟨.node left key right, cs⟩) valid keys validKeys
  refine ⟨out, completed, sourceEq, preserved, executed, ?_, by omega⟩
  intro nonempty
  cases keys with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => exact executed.prepend trace

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
