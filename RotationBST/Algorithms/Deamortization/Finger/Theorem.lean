module

public import RotationBST.Algorithms.Deamortization.Finger.Initialization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Finger
open HeavyPath.Finger.History

/-- Theorem 6 in the persistent pointer model. An offline source may select its
request strategy using the entire input. A fixed strategy gives the online
case, with literal emitted-code and request-cost prefix preservation. Initial
reshaping is separate from execution on the theorem's chosen starting tree. -/
theorem deamortize {α : Type} (family : List Nat → Simulation.Requests.Algorithm α)
    (c : LabelledCursor.Config α) (live : c.focus ≠ .nil) :
    ∃ (s : State α) (startup : Nat) (program : List Nat → Option Scheduler.Output),
      Simulation.ConfigValid (fun _ => 1) c s ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨s.pair.tree, []⟩ startup ∧ startup ≤ 16 * c.tree.erase.size ∧
      (∀ keys, (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, program keys = some out ∧
          Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some out.state.cursor ∧
          Scheduler.ServedStream ⟨s.pair.tree, []⟩ keys out.state.cursor out.instructions out.costs ∧
          Multifinger.Execution (Scheduler.cursorState ⟨s.pair.tree, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          out.instructions.length ≤ 1240 * ((family keys).runFrom [] c keys).1.length ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 c.tree.erase.size) ∧
      ((∃ a, ∀ keys, family keys = a) →
        ∀ xs ys out, program (xs ++ ys) = some out →
          ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
            first.costs <+: out.costs) := by
  obtain ⟨sourcePolicy, scheduler, _, s, startup, _, _, valid, _, trace, setup, _, execute⟩ :=
    minimized_transform c live
  let program := fun keys => transform sourcePolicy scheduler (family keys) [] c s keys
  refine ⟨s, startup, program, valid, trace, setup, ?_, ?_⟩
  · intro keys validKeys
    exact execute (family keys) [] keys validKeys
  · rintro ⟨a, fixed⟩ xs ys out completed
    change transform sourcePolicy scheduler (family (xs ++ ys)) [] c s (xs ++ ys) = some out at completed
    rw [fixed] at completed
    obtain ⟨first, firstRun, codePrefix, costPrefix⟩ :=
      transform_prefix sourcePolicy scheduler a [] c s xs ys completed
    refine ⟨first, ?_, codePrefix, costPrefix⟩
    change transform sourcePolicy scheduler (family xs) [] c s xs = some first
    rw [fixed]
    exact firstRun

end RotationBST.Deamortization.Finger
