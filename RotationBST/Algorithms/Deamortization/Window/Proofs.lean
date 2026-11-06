module

public import RotationBST.Models.Pointer.Detour.Abstract
public import RotationBST.Bounds.StaticTree.Trace.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Window
open Pointer

/-- One scheduler window consumes at most the budget from a pending physical
program. It either uses an existing visit or inserts a bounded excursion.
Every extra movement is charged to consumed original work, and the exact
remaining program resumes from the returned cursor. -/
theorem serve {start finish : Config} {ops : List Multifinger.Opcode}
    (executed : Multifinger.replay ops start = some finish) (live : start.focus ≠ .nil)
    {target budget : Nat} (valid : target < start.tree.size)
    (visits : ∃ cut visited, cut ≤ ops.length ∧
      Multifinger.replay (ops.take cut) start = some visited ∧ visited.key? = some target)
    (height : ∀ cut middle, Multifinger.replay (ops.take cut) start = some middle →
      ∀ x < middle.tree.size, Tree.depth middle.tree x ≤ budget) :
    ∃ (consumed : Nat) (middle visited : Config) (before after : List Multifinger.Opcode),
      consumed ≤ budget ∧ consumed ≤ ops.length ∧
      Multifinger.replay (ops.take consumed) start = some middle ∧
      Multifinger.replay (ops.drop consumed) middle = some finish ∧
      Multifinger.replay before start = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some middle ∧
      before.length + after.length ≤ 5 * consumed ∧
      1 + before.length + after.length ≤ 1 + 5 * budget ∧
      (consumed = budget ∨ middle.key? = some target) := by
  classical
  by_cases early : ∃ cut visited, cut ≤ budget ∧ cut ≤ ops.length ∧
      Multifinger.replay (ops.take cut) start = some visited ∧ visited.key? = some target
  · obtain ⟨cut, visited, within, length, first, key⟩ := early
    have split : Multifinger.replay (ops.take cut ++ ops.drop cut) start = some finish := by
      simpa only [List.take_append_drop] using executed
    have last : Multifinger.replay (ops.drop cut) visited = some finish := by
      simpa only [Multifinger.replay_append, first, Option.bind_some] using split
    refine ⟨cut, visited, visited, ops.take cut, [], within, length, first, last, first, key, rfl, ?_, ?_, Or.inr key⟩
    · simp only [List.length_take, List.length_nil]
      omega
    · simp only [List.length_take, List.length_nil]
      omega
  · have enough : budget ≤ ops.length := by
      obtain ⟨cut, visited, length, replay, key⟩ := visits
      by_contra short
      apply early
      exact ⟨cut, visited, by omega, length, replay, key⟩
    obtain ⟨middle, first, last, _⟩ := StaticTree.Trace.Results.replay_prefix_depth executed budget
    have trace := Multifinger.Replay.Results.physical first
    have middleLive := Pointer.Detour.Results.trace_nonempty trace live
    have size : start.tree.size = middle.tree.size := by
      obtain ⟨_, _, rotations⟩ := trace.rotations
      exact rotations.size_eq
    have depthBound : ∀ x < middle.tree.size, (Tree.depth middle.tree x : ℝ) ≤ budget := by
      intro x hx
      exact_mod_cast height budget middle first x hx
    obtain ⟨visited, outward, backward, reached, key, returned, work, _, _, _⟩ :=
      Pointer.Detour.Results.bounded middleLive (by rw [← size]; exact valid) depthBound
    have workNat : outward.length + backward.length ≤ 4 * budget := by
      have realBound : ((outward.length + backward.length : Nat) : ℝ) ≤ (4 * budget : Nat) := by
        push_cast
        linarith
      exact_mod_cast realBound
    refine ⟨budget, middle, visited, ops.take budget ++ outward, backward,
      le_rfl, enough, first, last, ?_, key, returned, ?_, ?_, Or.inl rfl⟩
    · simpa only [Multifinger.replay_append, first, Option.bind_some] using reached
    · simp only [List.length_append, List.length_take]
      omega
    · simp only [List.length_append, List.length_take]
      omega

end RotationBST.Deamortization.Window
