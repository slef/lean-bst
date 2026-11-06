module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Execution
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

/-- Request-by-request simulation is exactly the fixed policy applied to the
concatenated source program, so instruction-prefix certificates apply unchanged. -/
theorem flatten {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) {out : Output α}
    (completed : run p a past c s keys = some out) :
    Simulation.run p c s (a.runFrom past c keys).1 = some out ∧
      sourceRun c (a.runFrom past c keys).1 = some (a.runFrom past c keys).2 := by
  induction keys generalizing past c s out with
  | nil =>
    simp only [run, Option.some.injEq] at completed
    subst out
    exact ⟨rfl, rfl⟩
  | cons key keys ih =>
    have search := a.correct past c key (config_nonempty valid) (validKeys key (by simp))
    obtain ⟨first, firstRun, firstEq, firstValid, _, _, _⟩ := serves policyValid valid search
    have size := source_size search.legal
    have restValid : ∀ x ∈ keys, x < first.source.tree.erase.size := by
      intro x hx
      rw [firstEq, ← size]
      exact validKeys x (by simp [hx])
    simp only [run, firstRun, Option.bind_some] at completed
    cases lastEq : run p a (past ++ [key]) first.source first.state keys with
    | none => simp [lastEq] at completed
    | some last =>
      simp only [lastEq, Option.map_some, Option.some.injEq] at completed
      subst out
      obtain ⟨physical, legal⟩ := ih (past ++ [key]) firstValid restValid lastEq
      rw [firstEq] at physical legal
      constructor
      · simp only [Algorithm.runFrom, Simulation.run_append, firstRun, Option.bind_some,
          firstEq, physical, Option.map_some]
      · simp only [Algorithm.runFrom, source_append, search.legal, Option.bind_some, legal]

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
