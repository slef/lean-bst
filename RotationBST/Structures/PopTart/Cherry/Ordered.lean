module

public import RotationBST.Structures.PopTart.Cherry.Fringe
public import RotationBST.Structures.PopTart.Fringe
public import RotationBST.Structures.PopTart.Cherry.Programs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

/-- Ordered pushes preserve the entire nonincreasing weighted fringe. -/
theorem push_ordered {layers : Layers} {crumb bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (newOrdered : crumb.Ordered)
    (dominates : ∀ a ∈ crumb.fringe, ∀ b ∈ (layers.decode bottom).fringe, b.2 ≤ a.2) :
    ((layers.push crumb).decode bottom).Ordered :=
  (ordered_append (push_fringe layers crumb bottom)).mpr ⟨newOrdered, ordered, dominates⟩

/-- A single new leaf need only dominate each older weight individually. -/
theorem push_leaf_ordered {layers : Layers} {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (subtree : Tree) (weight : ℝ)
    (nonnegative : 0 ≤ weight)
    (dominates : ∀ b ∈ (layers.decode bottom).fringe, b.2 ≤ weight) :
    ((layers.push (.leaf subtree weight)).decode bottom).Ordered := by
  apply push_ordered ordered
  · exact ⟨nonnegative, by simp [fringe]⟩
  · simpa only [fringe, List.mem_singleton, forall_eq] using dominates

/-- Removing the first crumb preserves the weight order of the remainder. -/
theorem pop_ordered {layers rest : Layers} {crumb bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (popped : layers.pop = some (crumb, rest)) :
    crumb.Ordered ∧ (rest.decode bottom).Ordered := by
  have retained := (ordered_append (pop_fringe popped bottom)).mp ordered
  exact ⟨retained.1, retained.2.1⟩

theorem operation_ordered {level : Nat} {layers rest : Layers}
    (op : Operation level layers rest) {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (increasing : op.Increasing bottom) :
    (rest.decode bottom).Ordered := by
  cases op with
  | push crumb perfect => exact push_ordered ordered increasing.1 increasing.2
  | pop rest crumb popped => exact (pop_ordered ordered popped).2

/-- The same concrete programs retain the order under arbitrary pops and
pushes whose new weights dominate those currently present. -/
theorem sequence_ordered {level : Nat} {layers rest : Layers} {n : Nat}
    (program : Program level layers rest n) {bottom : WeightedTree}
    (ordered : (layers.decode bottom).Ordered) (increasing : program.Increasing bottom) :
    (rest.decode bottom).Ordered := by
  induction program with
  | nil => exact ordered
  | cons op tail ih => exact ih (operation_ordered op ordered increasing.1) increasing.2

end RotationBST.PopTart.Cherry
