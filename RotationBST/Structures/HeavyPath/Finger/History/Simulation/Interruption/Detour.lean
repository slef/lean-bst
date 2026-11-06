module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Proofs
public import RotationBST.Models.Pointer.Detour.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Interruption
open LabelledCursor

/-- Any physical interruption admits a logarithmic read-only request and an
exact return to the suspended cursor. The same pending suffix then resumes,
even when the interruption occurs away from a source-instruction boundary. -/
theorem run_detour {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      middle.focus ≠ .nil ∧
      ∀ x < s.pair.tree.size, ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
        Multifinger.replay before middle = some visited ∧ visited.key? = some x ∧
        Multifinger.replay after visited = some middle ∧
        (1 + before.length + after.length : ℝ) ≤ 197 + 156 * Real.logb 2 s.pair.tree.size ∧
        (middle.key? = some x → before = [] ∧ after = []) ∧
        Multifinger.replay (out.instructions.take cut ++ before ++ after ++ out.instructions.drop cut)
          ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
        (∀ pause, ∃ cursor, Multifinger.replay (before.take pause) middle = some cursor ∧
          cursor.tree = middle.tree) ∧
        (∀ pause, ∃ cursor, Multifinger.replay (after.take pause) visited = some cursor ∧
          cursor.tree = middle.tree) := by
  obtain ⟨middle, first, last, depths⟩ := run_uniform_prefix bounded valid completed cut
  have trace := Multifinger.Replay.Results.physical first
  have live := Pointer.Detour.Results.trace_nonempty trace (by simp [Pair.tree])
  have size : s.pair.tree.size = middle.tree.size := by
    obtain ⟨_, _, rotations⟩ := trace.rotations
    exact rotations.size_eq
  have height : ∀ x < middle.tree.size, (Tree.depth middle.tree x : ℝ) ≤
      49 + 39 * Real.logb 2 s.pair.tree.size := by
    simpa only [← size] using depths
  refine ⟨middle, first, last, live, ?_⟩
  intro x hx
  obtain ⟨visited, before, after, outward, visitedKey, backward, work, repeated, firstFixed, lastFixed⟩ :=
    Pointer.Detour.Results.bounded live (by rw [← size]; exact hx) height
  refine ⟨visited, before, after, outward, visitedKey, backward, ?_, repeated,
    Pointer.Detour.Results.resume first outward backward last, firstFixed, lastFixed⟩
  linarith

end RotationBST.HeavyPath.Finger.History.Simulation.Interruption
