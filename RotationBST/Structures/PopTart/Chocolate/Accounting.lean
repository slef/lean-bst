module

public import RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

/-- Carries are paid by the current full layer. Frozen next layers keep their
credits inside the icing, rather than losing them at the freeze boundary. -/
theorem push_amortized (stack : Layer) (new : WeightedTree) :
    stack.pushCost + (stack.push new).potential ≤ 20 + stack.potential := by
  classical
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]
    | one a => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]; omega
    | two a b => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]
    | three a b c =>
      by_cases thin : (.node b c : WeightedTree).mass < icing.decode.mass
      · simp only [Layer.pushCost, Layer.push, thin, ite_true, Layer.potential, Icing.potential, Regulars.potential]
        omega
      · simp only [Layer.pushCost, Layer.push, thin, ite_false, Layer.potential, Icing.potential, Regulars.potential]
        omega
  | next rs child icing =>
    cases rs with
    | zero => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]; omega
    | one a => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]; omega
    | two a b => simp [Layer.pushCost, Layer.push, Layer.potential, Regulars.potential]; omega
    | three a b c =>
      have ih := push_amortized child (.node b c)
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · simp only [Layer.pushCost, Layer.push, thin, ite_true, Layer.potential, Regulars.potential]
        omega
      · simp only [Layer.pushCost, Layer.push, thin, ite_false, Layer.potential, Icing.potential, Regulars.potential]
        omega
termination_by stack

end RotationBST.PopTart.Chocolate
