module

public import RotationBST.Structures.PopTart.Chocolate.Invariant
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

private theorem push_ne_nil (stack : Layer) (new : WeightedTree) :
    (stack.push new).decode.tree ≠ .nil := by
  classical
  cases stack with
  | last rs icing =>
    cases rs <;> simp only [Layer.push]
    all_goals first | (intro h; cases h) | (split <;> intro h <;> cases h)
  | next rs child icing =>
    cases rs <;> simp only [Layer.push]
    all_goals first | (intro h; cases h) | (split <;> intro h <;> cases h)

/-- Every push has an exact pointer realization. Freezing changes only the
structural interpretation after the rotations; no frozen interior is visited. -/
theorem push_trace (stack : Layer) (new : WeightedTree) :
    Pointer.Trace ⟨.node new.tree stack.decode.tree, []⟩
      ⟨(stack.push new).decode.tree, []⟩ stack.pushCost := by
  classical
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => exact .refl
    | one a => exact .refl
    | two a b => exact .refl
    | three a b c =>
      have join : Pointer.Trace
          ⟨.node b.tree (.node c.tree icing.decode.tree), []⟩
          ⟨.node (.node b.tree c.tree) icing.decode.tree, []⟩ 2 :=
        .step .downRight (.step .rotateRightChild .refl)
      have trace := join.inContext (by intro h; cases h) (by intro h; cases h)
        [.right a.tree, .right new.tree]
      by_cases thin : (.node b c : WeightedTree).mass < icing.decode.mass
      · simp only [Layer.push, thin, ite_true, Layer.pushCost]
        convert trace using 1 <;> rfl
      · simp only [Layer.push, thin, ite_false, Layer.pushCost]
        convert trace using 1 <;> rfl
  | next rs child icing =>
    cases rs with
    | zero => exact .refl
    | one a => exact .refl
    | two a b => exact .refl
    | three a b c =>
      have join : Pointer.Trace
          ⟨.node b.tree (.node c.tree (.node child.decode.tree icing.decode.tree)), []⟩
          ⟨.node (.node b.tree c.tree) (.node child.decode.tree icing.decode.tree), []⟩ 2 :=
        .step .downRight (.step .rotateRightChild .refl)
      have move : Pointer.Trace
          ⟨.node (.node b.tree c.tree) (.node child.decode.tree icing.decode.tree), []⟩
          ⟨.node (.node (.node b.tree c.tree) child.decode.tree) icing.decode.tree, []⟩ 2 :=
        .step .downRight (.step .rotateRightChild .refl)
      have localTrace := join.append move
      have first := localTrace.inContext (by intro h; cases h) (by intro h; cases h)
        [.right a.tree, .right new.tree]
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · have second := (push_trace child (.node b c)).inContext (by intro h; cases h)
          (push_ne_nil child (.node b c)) [.left icing.decode.tree, .right a.tree, .right new.tree]
        have linked := first.append second
        simp only [Layer.push, Layer.pushCost, thin, ite_true]
        convert linked using 1 <;> (try rfl)
        simp only [List.length_cons, List.length_nil]
        omega
      · simp only [Layer.push, Layer.pushCost, thin, ite_false]
        convert first using 1 <;> rfl
termination_by stack

end RotationBST.PopTart.Chocolate
