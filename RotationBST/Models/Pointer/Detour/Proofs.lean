module

public import RotationBST.Bounds.LazyFinger.ReadonlyWalk
public import RotationBST.Models.Pointer.Location
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Pointer.Detour

/-- A physical trace starting on an actual key cannot end at an empty focus. -/
theorem trace_nonempty {a b : Config} {cost : Nat} (trace : Trace a b cost)
    (live : a.focus ≠ .nil) : b.focus ≠ .nil := by
  induction trace with
  | refl => exact live
  | step step rest ih =>
    apply ih
    cases step <;> simp

private theorem reverse_walk {a b : Config} {cost : Nat} (walk : Walk a b cost) : Walk b a cost := by
  induction walk with
  | refl => exact .refl
  | step move rest ih =>
    simpa only [Nat.add_comm] using ih.append (Walk.step move.symm Walk.refl)

/-- Navigation to a requested key and back restores the entire cursor.
Both walks are bounded by the sum of the two keys' depths. -/
theorem walk {start : Config} {current target : Nat}
    (key : start.key? = some current) (valid : target < start.tree.size) :
    ∃ (visited : Config) (cost : Nat), visited.key? = some target ∧ visited.tree = start.tree ∧
      Walk start visited cost ∧ Walk visited start cost ∧
      cost ≤ Tree.depth start.tree current + Tree.depth start.tree target ∧
      (current = target → cost = 0) := by
  obtain ⟨first, visited, firstTree, tree, firstKey, visitedKey, forward⟩ :=
    LazyFinger.readonly_walk start.tree current target (start.key_lt_size current key) valid
  have same : first = start := Config.ext_key firstTree firstKey key
  subst first
  refine ⟨visited, _, visitedKey, tree, forward, reverse_walk forward, ?_, ?_⟩
  · have identity := LazyFinger.distance_add_twice_lca start.tree current target
    omega
  · intro same
    subst target
    exact LazyFinger.distance_self _ _ (start.key_lt_size current key)

private theorem move_code {a b : Config} (move : Move a b) :
    ∃ op : Multifinger.Opcode, Multifinger.perform op a = some b := by
  cases move with
  | downLeft => exact ⟨.downLeft, rfl⟩
  | downRight => exact ⟨.downRight, rfl⟩
  | upLeft => exact ⟨.upLeft, rfl⟩
  | upRight => exact ⟨.upRight, rfl⟩

/-- Record navigation while retaining its fixed tree at every physical prefix.
This is stronger than recording a trace with matching endpoint trees. -/
theorem record {a b : Config} {cost : Nat} (walk : Walk a b cost) :
    ∃ ops : List Multifinger.Opcode, ops.length = cost ∧ Multifinger.replay ops a = some b ∧
      ∀ cut, ∃ middle, Multifinger.replay (ops.take cut) a = some middle ∧ middle.tree = a.tree := by
  induction walk with
  | @refl a =>
    refine ⟨[], rfl, rfl, ?_⟩
    intro cut
    exact ⟨a, by simp [Multifinger.replay], rfl⟩
  | @step a b c cost move rest ih =>
    obtain ⟨op, performed⟩ := move_code move
    obtain ⟨ops, length, replay, prefixes⟩ := ih
    refine ⟨op :: ops, by simp [length], ?_, ?_⟩
    · simp only [Multifinger.replay, performed, Option.bind_some, replay]
    · intro cut
      cases cut with
      | zero => exact ⟨a, rfl, rfl⟩
      | succ cut =>
        obtain ⟨middle, prefixReplay, tree⟩ := prefixes cut
        refine ⟨middle, ?_, tree.trans move.tree_eq.symm⟩
        simpa only [List.take_succ_cons, Multifinger.replay, performed, Option.bind_some] using prefixReplay

/-- A bounded-height tree supplies a replayable read-only excursion from any
live cursor. The request charge is explicit, and repeated keys need no moves. -/
theorem bounded {start : Config} (live : start.focus ≠ .nil) {target : Nat}
    (valid : target < start.tree.size) {height : ℝ}
    (depths : ∀ x < start.tree.size, (Tree.depth start.tree x : ℝ) ≤ height) :
    ∃ (visited : Config) (before after : List Multifinger.Opcode),
      Multifinger.replay before start = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some start ∧
      (1 + before.length + after.length : ℝ) ≤ 1 + 4 * height ∧
      (start.key? = some target → before = [] ∧ after = []) ∧
      (∀ cut, ∃ middle, Multifinger.replay (before.take cut) start = some middle ∧ middle.tree = start.tree) ∧
      (∀ cut, ∃ middle, Multifinger.replay (after.take cut) visited = some middle ∧ middle.tree = start.tree) := by
  have key : ∃ current, start.key? = some current := by
    cases focus : start.focus with
    | nil => exact False.elim (live focus)
    | node l r => exact ⟨offset start.context + l.size, by simp [Config.key?, focus]⟩
  obtain ⟨current, key⟩ := key
  obtain ⟨visited, cost, visitedKey, tree, forward, backward, work, repeated⟩ := walk key valid
  obtain ⟨before, beforeLength, beforeReplay, beforePrefixes⟩ := record forward
  obtain ⟨after, afterLength, afterReplay, afterPrefixes⟩ := record backward
  refine ⟨visited, before, after, beforeReplay, visitedKey, afterReplay, ?_, ?_, beforePrefixes, ?_⟩
  · have firstDepth := depths current (start.key_lt_size current key)
    have targetDepth := depths target valid
    have workReal : (cost : ℝ) ≤ Tree.depth start.tree current + Tree.depth start.tree target := by
      exact_mod_cast work
    rw [beforeLength, afterLength]
    linarith
  · intro already
    have same : current = target := Option.some.inj (key.symm.trans already)
    have zero := repeated same
    exact ⟨List.length_eq_zero_iff.mp (beforeLength.trans zero), List.length_eq_zero_iff.mp (afterLength.trans zero)⟩
  · simpa only [tree] using afterPrefixes

/-- Insert a visit between an exact physical prefix and suffix. Returning to
the same cursor makes the original suffix executable without recomputation. -/
theorem resume {start middle visited finish : Config}
    {earlier before after later : List Multifinger.Opcode}
    (first : Multifinger.replay earlier start = some middle)
    (outward : Multifinger.replay before middle = some visited)
    (backward : Multifinger.replay after visited = some middle)
    (last : Multifinger.replay later middle = some finish) :
    Multifinger.replay (earlier ++ before ++ after ++ later) start = some finish := by
  simp only [Multifinger.replay_append, first, outward, backward, last, Option.bind_some]

end RotationBST.Pointer.Detour
