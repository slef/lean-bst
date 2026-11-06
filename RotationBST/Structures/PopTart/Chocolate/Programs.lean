module

public import RotationBST.Structures.PopTart.Chocolate.Traces
public import RotationBST.Structures.PopTart.Chocolate.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Arbitrary push histories retain validity, all exact pointer boundary
traces, and a single telescoping potential inequality. -/
theorem push_sequence {level : Nat} {stack rest : Layer} {n : Nat}
    (program : Pushes level stack rest n) (valid : stack.Valid level) :
    rest.Valid level ∧ program.Realizes ∧ program.cost + rest.potential ≤ 20 * n + stack.potential := by
  induction program with
  | nil stack => exact ⟨valid, .nil stack, by simp [Pushes.cost]⟩
  | @cons stack rest n new perfect nonnegative tail ih =>
    obtain ⟨validRest, realized, bound⟩ := ih (push_valid valid perfect nonnegative)
    have first := push_amortized stack new
    exact ⟨validRest, .cons (push_trace stack new) realized, by simp only [Pushes.cost]; omega⟩

/-- Starting with one bottom crumb, the rebalancing plus one unit per push
is at most `21m`. No ordering restriction is placed on new weights. -/
theorem empty_push_sequence {level : Nat} {bottom : WeightedTree} {rest : Layer} {n : Nat}
    (program : Pushes level (.last .zero (.base bottom)) rest n)
    (base : Perfect level bottom) (nonnegative : bottom.Nonnegative) :
    rest.Valid level ∧ program.Realizes ∧ n + program.cost ≤ 21 * n := by
  have initial : (Layer.last .zero (.base bottom)).Valid level :=
    ⟨trivial, ⟨base, nonnegative⟩, fun _ => ⟨bottom, rfl⟩⟩
  obtain ⟨valid, realized, bound⟩ := push_sequence program initial
  exact ⟨valid, realized, by simp only [Layer.potential, Icing.potential, Regulars.potential] at bound; omega⟩

end RotationBST.PopTart.Chocolate
