module

public import RotationBST.Algorithms.Combination.Worker.Replay.Requests.Abstract
public import RotationBST.Algorithms.Deamortization.Finger.Abstract
public import RotationBST.Models.Labelled.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Replay
open Combo.Worker HeavyPath.Finger.History

/-- Every causal rooted replay planner admits one causal deamortized physical
program. The setup is a separate linear trace; the exact response costs are
bounded by the planner's recorded work and individually logarithmic. Private
planning and stored programs remain resources of the abstract BST model. -/
theorem deamortize {σ : Type} {saved : Tree} (planner : Combo.Worker.Replay.Planner σ saved)
    (side : Bool) (nonempty : saved ≠ .nil) :
    ∃ (initial : Tree) (startup : Nat) (program : List Nat → Option Scheduler.Output),
      Pointer.Trace ⟨saved, []⟩ ⟨initial, []⟩ startup ∧ startup ≤ 16 * saved.size ∧
      (∀ keys, (∀ x ∈ keys, x < saved.size) →
        ∃ out, program keys = some out ∧
          Multifinger.replay out.instructions ⟨initial, []⟩ = some out.state.cursor ∧
          Scheduler.ServedStream ⟨initial, []⟩ keys out.state.cursor out.instructions out.costs ∧
          Multifinger.Execution (Scheduler.cursorState ⟨initial, []⟩) keys
            (Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
          out.costs.length = keys.length ∧ out.costs.sum = keys.length + out.instructions.length ∧
          out.costs.sum ≤ 1240 * (Combo.Worker.Replay.run planner side (planner.initial side) keys).2 ∧
          ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 saved.size) ∧
      (∀ xs ys out, program (xs ++ ys) = some out →
        ∃ first, program xs = some first ∧ first.instructions <+: out.instructions ∧
          first.costs <+: out.costs) := by
  let c : LabelledCursor.Config Nat := ⟨saved.labelFrom 0, []⟩
  have erased : c.erase = ⟨saved, []⟩ := by
    simp [c, LabelledCursor.Config.erase]
  have tree : c.tree.erase = saved := by
    simpa only [c, LabelledCursor.Config.tree, LabelledCursor.plug] using Representation.erase_label saved 0
  have live : c.focus ≠ .nil := by
    intro empty
    have := congrArg LabelledTree.erase empty
    change (saved.labelFrom 0).erase = Tree.nil at this
    rw [Representation.erase_label] at this
    exact nonempty this
  obtain ⟨a, aligned⟩ := Combo.Worker.Replay.Requests.planner_source (α := Nat) planner side
  obtain ⟨s, startup, program, _, trace, setup, executes, causal⟩ :=
    Finger.Results.deamortize (fun _ => a) c live
  rw [tree] at trace setup executes
  refine ⟨s.pair.tree, startup, program, trace, setup, ?_, causal ⟨a, fun _ => rfl⟩⟩
  intro keys valid
  obtain ⟨out, completed, replay, served, execution, bound, length, total, worst⟩ := executes keys valid
  have cost := (aligned [] c keys (by simp)
    (by simpa only [Combo.Worker.Replay.run, planner.initial_tree] using erased) valid).2.2
  simp only [Combo.Worker.Replay.run] at cost
  refine ⟨out, completed, replay, served, execution, length, total, ?_, worst⟩
  omega

end RotationBST.Deamortization.Replay
