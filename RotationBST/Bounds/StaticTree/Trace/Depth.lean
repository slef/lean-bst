module

public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import RotationBST.Models.Pointer.Basic
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.StaticTree.Trace
open _root_.RotationBST.Tree (depth)

private theorem root_depth (a b c : Tree) (x : Nat) :
    depth (.node (.node a b) c) x ≤ depth (.node a (.node b c)) x + 1 ∧
    depth (.node a (.node b c)) x ≤ depth (.node (.node a b) c) x + 1 := by
  have index : x - (a.size + 1 + b.size) - 1 = x - a.size - 1 - b.size - 1 := by omega
  simp only [depth, Tree.size, index]
  split_ifs <;> omega

/-- A rotation at any depth changes every rank's depth by at most one. -/
theorem rotate_depth {s t : Tree} (rotation : Rotate s t) (x : Nat) :
    depth t x ≤ depth s x + 1 := by
  induction rotation generalizing x with
  | right => exact (root_depth _ _ _ x).2
  | left => exact (root_depth _ _ _ x).1
  | @inLeft a b c rotation ih =>
    have bound := ih x
    have size := rotation.size_eq
    simp only [depth, ← size]
    split_ifs <;> omega
  | @inRight a b c rotation ih =>
    have bound := ih (x - c.size - 1)
    simp only [depth]
    split_ifs <;> omega

/-- Depth drift is bounded by the number of actual rotations. -/
theorem rotations_depth {s t : Tree} {cost : Nat} (rotations : Rotations s t cost) (x : Nat) :
    depth t x ≤ depth s x + cost := by
  induction rotations with
  | refl => omega
  | step rotation rest ih =>
    have first := rotate_depth rotation x
    omega

/-- Pointer movements do not change the tree; allowing one rotation per
instruction bounds every rank's depth after any physical trace. -/
theorem trace_depth {s t : Pointer.Config} {cost : Nat} (trace : Pointer.Trace s t cost) (x : Nat) :
    depth t.tree x ≤ depth s.tree x + cost := by
  obtain ⟨rotations, bound, executed⟩ := trace.rotations
  have drift := rotations_depth executed x
  omega

/-- The same comparison holds toward the starting endpoint. This is a shape
comparison and does not charge a physically reversed pointer program. -/
theorem trace_depth_reverse {s t : Pointer.Config} {cost : Nat} (trace : Pointer.Trace s t cost) (x : Nat) :
    depth s.tree x ≤ depth t.tree x + cost := by
  obtain ⟨rotations, bound, executed⟩ := trace.rotations
  have drift := rotations_depth executed.symm x
  omega

/-- Every successful physical prefix is bounded from both endpoints, with
exactly the instruction counts before and after the interruption. -/
theorem replay_prefix_depth {ops : List Multifinger.Opcode} {s t : Pointer.Config}
    (executed : Multifinger.replay ops s = some t) (cut : Nat) :
    ∃ middle, Multifinger.replay (ops.take cut) s = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some t ∧
      ∀ x, depth middle.tree x ≤ min (depth s.tree x + (ops.take cut).length)
        (depth t.tree x + (ops.drop cut).length) := by
  have split : Multifinger.replay (ops.take cut ++ ops.drop cut) s = some t := by
    simpa only [List.take_append_drop] using executed
  rw [Multifinger.replay_append] at split
  cases first : Multifinger.replay (ops.take cut) s with
  | none => simp [first] at split
  | some middle =>
    have last : Multifinger.replay (ops.drop cut) middle = some t := by
      simpa only [first, Option.bind_some] using split
    refine ⟨middle, rfl, last, ?_⟩
    intro x
    exact le_min (trace_depth (Multifinger.Replay.Results.physical first) x)
      (trace_depth_reverse (Multifinger.Replay.Results.physical last) x)

/-- A real-valued cost budget bounds every interruption point, including
cuts past the end of the emitted code. -/
theorem replay_prefix_bound {ops : List Multifinger.Opcode} {s t : Pointer.Config}
    (executed : Multifinger.replay ops s = some t) {budget : ℝ}
    (cost : (ops.length : ℝ) ≤ budget) (cut : Nat) :
    ∃ middle, Multifinger.replay (ops.take cut) s = some middle ∧
      Multifinger.replay (ops.drop cut) middle = some t ∧
      ∀ x, (depth middle.tree x : ℝ) ≤ depth s.tree x + budget := by
  obtain ⟨middle, first, last, depths⟩ := replay_prefix_depth executed cut
  refine ⟨middle, first, last, ?_⟩
  intro x
  have firstBound := (depths x).trans (min_le_left _ _)
  have length : (ops.take cut).length ≤ ops.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
  have realBound : (depth middle.tree x : ℝ) ≤ depth s.tree x + ops.length := by
    exact_mod_cast (show depth middle.tree x ≤ depth s.tree x + ops.length by omega)
  linarith

end RotationBST.StaticTree.Trace
