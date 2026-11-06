module

public import RotationBST.Structures.PopTart.Chocolate.Thaw
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Chocolate

theorem base_eq {child : Layer} {crumb : WeightedTree} (base : child.baseCrumb = some crumb) :
    child = .last .zero (.base crumb) := by
  cases child with
  | last rs icing => cases rs <;> cases icing <;> simp_all [Layer.baseCrumb]
  | next rs more icing => cases base

theorem hasTop_of_no_base {child : Layer} {level : Nat} (valid : child.Valid level)
    (noBase : child.baseCrumb = none) : child.HasTop := by
  cases child with
  | last rs icing =>
    cases rs with
    | zero =>
      obtain ⟨crumb, rfl⟩ := valid.2.2 rfl
      cases noBase
    | one | two | three => trivial
  | next rs more icing =>
    cases rs with
    | zero => exact False.elim (valid.2.2.2.1 rfl)
    | one | two | three => trivial

theorem pop_hasTop {stack rest : Layer} {crumb : WeightedTree}
    (popped : stack.pop = some (crumb, rest)) : stack.HasTop := by
  cases stack with
  | last rs icing => cases rs <;> trivial
  | next rs child icing => cases rs <;> trivial

theorem hasTop_ne_nil {stack : Layer} (top : stack.HasTop) : stack.decode.tree ≠ .nil := by
  cases stack with
  | last rs icing => cases rs <;> first | exact False.elim top | intro h; cases h
  | next rs child icing => cases rs <;> first | exact False.elim top | intro h; cases h

theorem pop_last (a : WeightedTree) (icing : Icing) :
    (Layer.last (.one a) icing).pop = icing.thaw.map (fun rest => (a, rest)) := rfl

theorem pop_next (a : WeightedTree) (child : Layer) (icing : Icing) :
    (Layer.next (.one a) child icing).pop = match child.baseCrumb with
      | some (.node b c) => some (a, .last (.two b c) icing)
      | some (.leaf _ _) => none
      | none => match child.pop with
          | some (.node b c, rest) => some (a, .next (.two b c) rest icing)
          | _ => none := rfl

theorem popCost_next (a : WeightedTree) (child : Layer) (icing : Icing) :
    (Layer.next (.one a) child icing).popCost = match child.baseCrumb with
      | some _ => 4
      | none => 10 + child.popCost := rfl

end RotationBST.PopTart.Chocolate
