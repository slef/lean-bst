module

public import RotationBST.Structures.PopTart.Chocolate.Depth
public import RotationBST.Structures.PopTart.Chocolate.Programs
public import RotationBST.Structures.PopTart.Chocolate.Population
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- The full weighted-depth estimate is realized by actual pointer access to
any nonempty original fringe subtree, including inside frozen icing blocks. -/
theorem weighted_access {stack : Layer} (valid : stack.Valid 0)
    {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt stack.decode subtree weight depth) (positive : 0 < weight) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = stack.decode.tree ∧
      Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨subtree, cs⟩ depth ∧
      (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (stack.decode.mass / weight) := by
  obtain ⟨cs, length, plugged, trace⟩ := slot_trace slot nonempty
  exact ⟨cs, length, plugged, trace, weighted_depth valid slot positive⟩

/-- Arbitrary-weight push histories retain the full weighted-depth bound as
well as their constant amortized cost and exact pointer boundary traces. -/
theorem weighted_push_sequence {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Pushes 0 (.last .zero (.base bottom)) rest n)
    (base : Perfect 0 bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid 0 ∧ program.Realizes ∧ n + program.cost ≤ 21 * n ∧
      ∀ subtree weight depth, SlotAt rest.decode subtree weight depth → 0 < weight →
        (depth : ℝ) ≤ 7 + 7 * Real.logb 2 (rest.decode.mass / weight) := by
  obtain ⟨valid, realizes, bound⟩ := empty_push_sequence program base nonnegative
  exact ⟨valid, realizes, bound, fun _ _ _ slot positive => weighted_depth valid slot positive⟩

end RotationBST.PopTart.Chocolate
