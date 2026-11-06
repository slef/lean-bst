module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Execution
public import RotationBST.Structures.HeavyPath.Finger.History.PotentialBound
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Requests
open LabelledCursor

theorem config_size {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : s.pair.tree.size = c.tree.erase.size := by
  cases c with
  | mk focus context =>
      cases focus with
      | nil => exact False.elim valid
      | node left key right => exact History.state_size valid

/-- Stored simulation credit is bounded at any valid cursor, independently
of the length or cost of the history producing that cursor. -/
theorem config_potential_bound {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : s.potential + 20 ≤ 20 * c.tree.erase.size := by
  cases c with
  | mk focus context =>
      cases focus with
      | nil => exact False.elim valid
      | node left key right => exact History.potential_bound valid

/-- A request fragment from an arbitrary valid representation pays only a
linear representation allowance, not the work of the preceding history. -/
theorem interval_work {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) (a : Algorithm α) (past : List Nat)
    {c : Config α} {s : State α} (valid : ConfigValid weight c s)
    (keys : List Nat) (validKeys : ∀ x ∈ keys, x < c.tree.erase.size) :
    ∃ out, run p a past c s keys = some out ∧ out.source = (a.runFrom past c keys).2 ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      Pointer.Execution s.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
      keys.length + out.cost ≤ 62 * (keys.length + (a.runFrom past c keys).1.length) +
        20 * c.tree.erase.size := by
  obtain ⟨out, completed, source, represented, replay, executed, bound⟩ :=
    run_spec policyValid a past valid keys validKeys
  have credit := config_potential_bound valid
  exact ⟨out, completed, source, represented, replay, executed, by omega⟩

end RotationBST.HeavyPath.Finger.History.Simulation.Requests
