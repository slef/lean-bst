module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Source
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

/-- A visit anywhere in a source search becomes an actual physical visit in
the emitted code. Later source work is retained, including rotations. -/
theorem serves_recorded {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {key : Nat} (valid : ConfigValid weight c s)
    (search : Serves c ops key final) :
    ∃ out, Simulation.run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      Pointer.Serves s.pair.tree out.state.pair.tree key (1 + out.cost) ∧
      ∃ cut visited, cut ≤ out.instructions.length ∧
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some visited ∧
        visited.key? = some key := by
  obtain ⟨before, after, visited, rfl, firstSource, touched, lastSource⟩ := search
  obtain ⟨first, firstRun, firstEq, firstValid, firstReplay, firstBound⟩ :=
    Simulation.Results.run_spec policyValid valid firstSource
  have remaining : sourceRun first.source after = some final := by simpa only [firstEq] using lastSource
  obtain ⟨last, lastRun, lastEq, lastValid, lastReplay, lastBound⟩ :=
    Simulation.Results.run_spec policyValid firstValid remaining
  refine ⟨⟨last.source, last.state, first.instructions ++ last.instructions⟩, ?_, lastEq,
    lastValid, ?_, ?_, ?_, ?_⟩
  · simp only [Simulation.Results.run_append, firstRun, Option.bind_some, lastRun, Option.map_some]
  · simpa only [Multifinger.replay_append, firstReplay, Option.bind_some] using lastReplay
  · simp only [Output.cost, List.length_append] at *
    omega
  · refine ⟨⟨first.state.pair.tree, []⟩, ⟨last.state.pair.tree, []⟩, first.cost, last.cost,
      Multifinger.Replay.Results.physical firstReplay, ?_,
      Multifinger.Replay.Results.physical lastReplay, rfl, ?_⟩
    · rw [Simulation.Results.root_key firstValid, firstEq]
      exact touched
    · simp only [Output.cost, List.length_append, Nat.add_assoc]

  · refine ⟨first.instructions.length, ⟨first.state.pair.tree, []⟩, ?_, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · simpa only [List.take_append_length] using firstReplay
    · rw [Simulation.Results.root_key firstValid, firstEq]
      exact touched

theorem serves {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {key : Nat} (valid : ConfigValid weight c s)
    (search : Serves c ops key final) :
    ∃ out, Simulation.run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      Pointer.Serves s.pair.tree out.state.pair.tree key (1 + out.cost) := by
  obtain ⟨out, completed, source, preserved, replay, bound, served, _⟩ :=
    serves_recorded policyValid valid search
  exact ⟨out, completed, source, preserved, replay, bound, served⟩

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
