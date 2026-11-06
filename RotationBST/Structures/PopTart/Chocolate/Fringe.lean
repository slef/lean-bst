module

public import RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract
public import RotationBST.Structures.PopTart.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Recursive carries and immediate freezing preserve every original fringe
occurrence in its original order, including occurrences inside frozen layers. -/
theorem push_fringe (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.fringe = new.fringe ++ stack.decode.fringe := by
  classical
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => rfl
    | one a => rfl
    | two a b => rfl
    | three a b c =>
      by_cases thin : (.node b c : WeightedTree).mass < icing.decode.mass
      · simp only [Layer.push, thin, ite_true, Layer.decode, Icing.decode, Regulars.attach, fringe,
          List.append_assoc]
      · simp only [Layer.push, thin, ite_false, Layer.decode, Icing.decode, Regulars.attach, fringe,
          List.append_assoc]
  | next rs child icing =>
    cases rs with
    | zero => rfl
    | one a => rfl
    | two a b => rfl
    | three a b c =>
      have ih := push_fringe child (.node b c)
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · simp only [Layer.push, thin, ite_true, Layer.decode, Regulars.attach, fringe, ih,
          List.append_assoc]
      · simp only [Layer.push, thin, ite_false, Layer.decode, Icing.decode, Regulars.attach, fringe,
          List.append_assoc]
termination_by stack

/-- The mass comparison in a recursive carry remains valid after rebalancing. -/
theorem push_mass (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.mass = new.mass + stack.decode.mass := by
  rw [← fringe_mass, push_fringe, List.map_append, List.sum_append, fringe_mass, fringe_mass]

end RotationBST.PopTart.Chocolate
