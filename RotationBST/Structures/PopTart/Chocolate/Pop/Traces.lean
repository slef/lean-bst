module

public import RotationBST.Structures.PopTart.Chocolate.Pop.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

/-- Every pop has its exact pointer trace, including recursive borrowing and
thawing, with the removed separator still exposed for the caller. -/
theorem pop_trace {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) :
    Pointer.Trace ⟨stack.decode.tree, []⟩ ⟨.node crumb.tree rest.decode.tree, []⟩ stack.popCost := by
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
        exact thaw_under thawed a
    | two a b => cases popped; exact .refl
    | three a b c => cases popped; exact .refl
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
          rw [popCost_next, base]
          have same := base_eq base
          subst child
          exact thaw_under (icing := .solid (.node b c) icing) rfl a
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
            have first := (pop_trace result).inContext (hasTop_ne_nil (pop_hasTop result))
              (by intro h; cases h) [.left icing.decode.tree, .right a.tree]
            have second := thaw_under (icing := .frozen (.node b c) suffix icing) rfl a
            have linked := first.append second
            rw [popCost_next, base]
            convert linked using 1 <;> (try rfl)
            simp only [List.length_cons, List.length_nil, Icing.popCost]
            omega
    | two a b => cases popped; exact .refl
    | three a b c => cases popped; exact .refl
termination_by stack

end RotationBST.PopTart.Chocolate
