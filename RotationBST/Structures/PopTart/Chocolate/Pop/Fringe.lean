module

public import RotationBST.Structures.PopTart.Chocolate.Pop.Equations
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate
open WeightedTree

/-- Pop removes precisely the first crumb, retaining the original fringe
occurrences through borrowing and thawing. -/
theorem pop_fringe {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    stack.decode.fringe = crumb.fringe ++ rest.decode.fringe := by
  cases stack with
  | last rs icing =>
    cases rs with
    | zero => cases popped
    | one a =>
      rw [pop_last] at popped
      cases thawed : icing.thaw with
      | none => simp only [thawed, Option.map_none] at popped; cases popped
      | some next =>
        simp only [thawed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at popped
        rcases popped with ⟨rfl, rfl⟩
        simp only [Layer.decode, Regulars.attach, fringe, thaw_fringe thawed]
    | two a b => cases popped; rfl
    | three a b c => cases popped; rfl
  | next rs child icing =>
    cases rs with
    | zero => cases popped
    | one a =>
      rw [pop_next] at popped
      cases base : child.baseCrumb with
      | some block =>
        cases block with
        | leaf => simp only [base] at popped; cases popped
        | node b c =>
          simp only [base, Option.some.injEq, Prod.mk.injEq] at popped
          rcases popped with ⟨rfl, rfl⟩
          have same := base_eq base
          subst child
          simp only [Layer.decode, Icing.decode, Regulars.attach, fringe, List.append_assoc]
      | none =>
        cases result : child.pop with
        | none => simp only [base, result] at popped; cases popped
        | some pair =>
          rcases pair with ⟨block, suffix⟩
          cases block with
          | leaf => simp only [base, result] at popped; cases popped
          | node b c =>
            simp only [base, result, Option.some.injEq, Prod.mk.injEq] at popped
            rcases popped with ⟨rfl, rfl⟩
            have retained := pop_fringe result
            simp only [Layer.decode, Regulars.attach, fringe, retained, List.append_assoc]
    | two a b => cases popped; rfl
    | three a b c => cases popped; rfl
termination_by stack

theorem pop_mass {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    stack.decode.mass = crumb.mass + rest.decode.mass := by
  rw [← fringe_mass, pop_fringe popped, List.map_append, List.sum_append, fringe_mass, fringe_mass]

end RotationBST.PopTart.Chocolate
