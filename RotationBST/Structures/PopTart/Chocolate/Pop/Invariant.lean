module

public import RotationBST.Structures.PopTart.Chocolate.Pop.Fringe
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Every valid nonempty layer pops successfully and returns a perfect,
nonnegative crumb, retaining structural validity and strict thick icing. -/
theorem pop_valid {stack : Layer} {level : Nat} (valid : stack.Valid level) (top : stack.HasTop) :
    ∃ crumb rest, stack.pop = some (crumb, rest) ∧ Perfect level crumb ∧ crumb.Nonnegative ∧ rest.Valid level := by
  cases stack with
  | last rs icing =>
    obtain ⟨regulars, ice, empty⟩ := valid
    cases rs with
    | zero => exact False.elim top
    | one a =>
      obtain ⟨rest, thawed, restored⟩ := thaw_valid ice
      exact ⟨a, rest, by rw [pop_last, thawed]; rfl, regulars.1, regulars.2, restored⟩
    | two a b =>
      exact ⟨a, _, rfl, regulars.1.1, regulars.1.2, regulars.2, ice, by intro h; cases h⟩
    | three a b c =>
      exact ⟨a, _, rfl, regulars.1.1, regulars.1.2, regulars.2, ice, by intro h; cases h⟩
  | next rs child icing =>
    obtain ⟨regulars, childValid, ice, nonempty, thick⟩ := valid
    cases rs with
    | zero => exact False.elim top
    | one a =>
      cases base : child.baseCrumb with
      | some block =>
        have same := base_eq base
        subst child
        have perfect := childValid.2.1.1
        have nonnegative := childValid.2.1.2
        cases perfect with
        | node pb pc =>
          exact ⟨a, _, rfl, regulars.1, regulars.2,
            ⟨⟨pb, nonnegative.1⟩, ⟨pc, nonnegative.2⟩⟩, ice, by intro h; cases h⟩
      | none =>
        obtain ⟨block, suffix, popped, perfect, nonnegative, restored⟩ :=
          pop_valid childValid (hasTop_of_no_base childValid base)
        have massEq := pop_mass popped
        have blockMass := mass_nonnegative nonnegative
        have thinner : suffix.decode.mass < icing.decode.mass := by linarith only [massEq, blockMass, thick]
        cases perfect with
        | node pb pc =>
          refine ⟨a, .next (.two _ _) suffix icing, ?_, regulars.1, regulars.2,
            ⟨⟨pb, nonnegative.1⟩, ⟨pc, nonnegative.2⟩⟩, restored, ice, (by intro h; cases h), thinner⟩
          rw [pop_next, base, popped]
    | two a b =>
      exact ⟨a, _, rfl, regulars.1.1, regulars.1.2, regulars.2, childValid, ice, (by intro h; cases h), thick⟩
    | three a b c =>
      exact ⟨a, _, rfl, regulars.1.1, regulars.1.2, regulars.2, childValid, ice, (by intro h; cases h), thick⟩
termination_by stack

theorem popped_valid {stack rest : Layer} {level : Nat} {crumb : WeightedTree}
    (valid : stack.Valid level) (popped : stack.pop = some (crumb, rest)) :
    Perfect level crumb ∧ crumb.Nonnegative ∧ rest.Valid level := by
  obtain ⟨other, suffix, same, perfect, nonnegative, restored⟩ := pop_valid valid (pop_hasTop popped)
  rw [popped] at same
  cases same
  exact ⟨perfect, nonnegative, restored⟩

end RotationBST.PopTart.Chocolate
