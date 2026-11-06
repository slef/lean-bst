module

public import RotationBST.Structures.PopTart.Chocolate.Fringe
public import RotationBST.Structures.PopTart.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

theorem attach_nonnegative {rs : Regulars} {level : Nat} (valid : rs.Valid level)
    {tail : WeightedTree} (nonnegative : tail.Nonnegative) : (rs.attach tail).Nonnegative := by
  cases rs with
  | zero => exact nonnegative
  | one a => exact ⟨valid.2, nonnegative⟩
  | two a b => exact ⟨valid.1.2, valid.2.2, nonnegative⟩
  | three a b c => exact ⟨valid.1.2, valid.2.1.2, valid.2.2.2, nonnegative⟩

mutual
theorem layer_nonnegative {stack : Layer} {level : Nat} (valid : stack.Valid level) :
    stack.decode.Nonnegative := by
  cases stack with
  | last rs icing => exact attach_nonnegative valid.1 (icing_nonnegative valid.2.1)
  | next rs child icing =>
    exact attach_nonnegative valid.1 ⟨layer_nonnegative valid.2.1, icing_nonnegative valid.2.2.1⟩
termination_by sizeOf stack

theorem icing_nonnegative {icing : Icing} {level : Nat} (valid : icing.Valid level) :
    icing.decode.Nonnegative := by
  cases icing with
  | base crumb => exact valid.2
  | solid crumb tail => exact ⟨valid.2.1, icing_nonnegative valid.2.2.1⟩
  | frozen carry old tail =>
    exact ⟨⟨valid.2.1, layer_nonnegative valid.2.2.1⟩, icing_nonnegative valid.2.2.2.1⟩
termination_by sizeOf icing
end

/-- A push preserves the perfect-crumb, nonnegative-weight, and thick-icing
invariants for arbitrary new nonnegative weights. Equality freezes the child. -/
theorem push_valid {stack : Layer} {level : Nat} (valid : stack.Valid level)
    {new : WeightedTree} (perfect : Perfect level new) (nonnegative : new.Nonnegative) :
    (stack.push new).Valid level := by
  classical
  cases stack with
  | last rs icing =>
    obtain ⟨regulars, ice, empty⟩ := valid
    cases rs with
    | zero => exact ⟨⟨perfect, nonnegative⟩, ice, by intro h; cases h⟩
    | one a => exact ⟨⟨⟨perfect, nonnegative⟩, regulars⟩, ice, by intro h; cases h⟩
    | two a b => exact ⟨⟨⟨perfect, nonnegative⟩, regulars⟩, ice, by intro h; cases h⟩
    | three a b c =>
      have joined : Perfect (level + 1) (.node b c) := .node regulars.2.1.1 regulars.2.2.1
      have joinedNonnegative : (.node b c : WeightedTree).Nonnegative := ⟨regulars.2.1.2, regulars.2.2.2⟩
      by_cases thin : (.node b c : WeightedTree).mass < icing.decode.mass
      · simp only [Layer.push, thin, ite_true]
        exact ⟨⟨⟨perfect, nonnegative⟩, regulars.1⟩,
          ⟨trivial, ⟨joined, joinedNonnegative⟩, fun _ => ⟨_, rfl⟩⟩,
          ice, (by intro h; cases h), thin⟩
      · simp only [Layer.push, thin, ite_false]
        exact ⟨⟨⟨perfect, nonnegative⟩, regulars.1⟩,
          ⟨joined, joinedNonnegative, ice, le_of_not_gt thin⟩, by intro h; cases h⟩
  | next rs child icing =>
    obtain ⟨regulars, childValid, ice, nonempty, thick⟩ := valid
    cases rs with
    | zero => exact False.elim (nonempty rfl)
    | one a => exact ⟨⟨⟨perfect, nonnegative⟩, regulars⟩, childValid, ice, (by intro h; cases h), thick⟩
    | two a b => exact ⟨⟨⟨perfect, nonnegative⟩, regulars⟩, childValid, ice, (by intro h; cases h), thick⟩
    | three a b c =>
      have joined : Perfect (level + 1) (.node b c) := .node regulars.2.1.1 regulars.2.2.1
      have joinedNonnegative : (.node b c : WeightedTree).Nonnegative := ⟨regulars.2.1.2, regulars.2.2.2⟩
      by_cases thin : (.node b c : WeightedTree).mass + child.decode.mass < icing.decode.mass
      · simp only [Layer.push, thin, ite_true]
        exact ⟨⟨⟨perfect, nonnegative⟩, regulars.1⟩, push_valid childValid joined joinedNonnegative,
          ice, (by intro h; cases h), by simpa only [push_mass] using thin⟩
      · simp only [Layer.push, thin, ite_false]
        exact ⟨⟨⟨perfect, nonnegative⟩, regulars.1⟩,
          ⟨joined, joinedNonnegative, childValid, ice, thick, le_of_not_gt thin⟩, by intro h; cases h⟩
termination_by sizeOf stack

end RotationBST.PopTart.Chocolate
