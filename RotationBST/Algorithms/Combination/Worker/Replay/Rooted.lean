module

public import RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import RotationBST.Models.Pointer.Navigation
public import RotationBST.Models.Pointer.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

private theorem finish_nonempty {a b : Pointer.Config} {k : Nat} (run : Pointer.Trace a b k)
    (start : a.focus ≠ .nil) : b.focus ≠ .nil := by
  induction run with
  | refl => exact start
  | step first rest ih => apply ih; cases first <;> simp

/-- A conventional request can be recorded as a root-to-root instruction log.
Returning from its final cursor costs at most the preceding trace length.
Two bookkeeping units in the replay worker fit within twice the original
request-inclusive cost, even for a zero-move access to the root. -/
theorem rooted {s t : Tree} {x cost : Nat} (served : Pointer.Serves s t x cost) :
    ∃ ops, replay ops ⟨s, []⟩ = some ⟨t, []⟩ ∧ Visits x ops ⟨s, []⟩ ∧ ops.length + 2 ≤ 2 * cost := by
  obtain ⟨visited, finish, before, after, first, key, last, tree, charged⟩ := served
  have nonempty : visited.focus ≠ .nil := by
    intro empty
    simp [Pointer.Config.key?, empty] at key
  have finalNonempty := finish_nonempty last nonempty
  have back : Pointer.Trace finish ⟨t, []⟩ finish.context.length := by
    rcases finish with ⟨focus, context⟩
    cases focus with
    | nil => exact False.elim (finalNonempty rfl)
    | node l r => simpa only [← tree, Pointer.Config.tree] using Pointer.ascend context l r
  obtain ⟨prefixOps, prefixLength, prefixRun⟩ := Multifinger.Replay.Results.record first
  obtain ⟨suffixOps, suffixLength, suffixRun⟩ := Multifinger.Replay.Results.record (last.append back)
  have depth := (first.append last).depth_le
  refine ⟨prefixOps ++ suffixOps, ?_, ⟨prefixOps, suffixOps, visited, rfl, prefixRun, key⟩, ?_⟩
  · rw [replay_append, prefixRun, Option.bind_some, suffixRun]
  · simp only [List.length_append, prefixLength, suffixLength]
    simp only [List.length_nil, Nat.zero_add] at depth
    omega

end RotationBST.Combo.Worker.Replay
