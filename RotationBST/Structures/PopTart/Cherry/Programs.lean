module

public import RotationBST.Structures.PopTart.Cherry.Traces
public import RotationBST.Structures.PopTart.Cherry.Depth
public import RotationBST.Structures.PopTart.Cherry.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry

/-- Each concrete operation preserves the layered invariant. -/
theorem operation_valid {level : Nat} {layers rest : Layers}
    (valid : Valid level layers) (op : Operation level layers rest) : Valid level rest := by
  cases op with
  | push crumb perfect => exact push_valid valid perfect
  | pop rest crumb popped => exact (popped_valid valid popped).2

theorem operation_trace {level : Nat} {layers rest : Layers}
    (op : Operation level layers rest) (bottom : WeightedTree) (cs : List Pointer.Frame) :
    Pointer.Trace ⟨op.input bottom, cs⟩ ⟨op.output bottom, cs⟩ op.cost := by
  cases op with
  | push crumb perfect => exact (push_trace layers crumb bottom).under cs
  | pop rest crumb popped => exact (pop_trace popped bottom).under cs

theorem operation_amortized {level : Nat} {layers rest : Layers} (op : Operation level layers rest) :
    op.cost + rest.potential ≤ 10 + layers.potential := by
  cases op with
  | push crumb perfect => exact push_amortized layers crumb
  | pop rest crumb popped => exact pop_amortized popped

/-- Arbitrary mixed histories preserve validity and have actual pointer
realizations with a single telescoping potential bound. -/
theorem sequence {level : Nat} {layers rest : Layers} {n : Nat}
    (program : Program level layers rest n) (valid : Valid level layers) (bottom : WeightedTree) :
    Valid level rest ∧ program.Realizes bottom ∧ program.cost + rest.potential ≤ 10 * n + layers.potential := by
  induction program with
  | nil layers => exact ⟨valid, .nil layers, by simp [Program.cost]⟩
  | @cons layers middle rest n op tail ih =>
    obtain ⟨validRest, realized, bound⟩ := ih (operation_valid valid op)
    have first := operation_amortized op
    exact ⟨validRest, .cons (operation_trace op bottom []) realized, by simp only [Program.cost]; omega⟩

/-- Empty initialization gives constant amortized cost even for mixed pushes
and pops. An extra unit per operation covers the operation/request itself. -/
theorem empty_sequence {level : Nat} {rest : Layers} {n : Nat}
    (program : Program level .nil rest n) (bottom : WeightedTree) :
    Valid level rest ∧ program.Realizes bottom ∧ n + program.cost ≤ 11 * n := by
  obtain ⟨valid, realized, bound⟩ := sequence program (.nil _) bottom
  exact ⟨valid, realized, by simp only [Layers.potential] at bound; omega⟩

end RotationBST.PopTart.Cherry
