module

public import RotationBST.Structures.PopTart.Cherry.Accounting
public import RotationBST.Models.Pointer.Navigation
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry

private theorem decode_ne_nil {layers : Layers} (nonempty : layers ≠ .nil) (bottom : WeightedTree) :
    (layers.decode bottom).tree ≠ .nil := by
  cases layers <;> first | exact False.elim (nonempty rfl) | intro h; cases h

private theorem push_ne_nil (layers : Layers) (crumb bottom : WeightedTree) :
    ((layers.push crumb).decode bottom).tree ≠ .nil := by
  cases layers <;> intro h <;> cases h

/-- Every carry is realized by actual pointer moves and a left rotation,
returning to the supplied root. Frozen fringe subtrees are never inspected. -/
theorem push_trace (layers : Layers) (crumb bottom : WeightedTree) :
    Pointer.Trace ⟨.node crumb.tree (layers.decode bottom).tree, []⟩
      ⟨((layers.push crumb).decode bottom).tree, []⟩ layers.pushCost := by
  induction layers generalizing crumb with
  | nil => exact .refl
  | one a tail ih => exact .refl
  | two a b tail ih => exact .refl
  | three a b c tail ih =>
    have join : Pointer.Trace
        ⟨.node b.tree (.node c.tree (tail.decode bottom).tree), []⟩
        ⟨.node (.node b.tree c.tree) (tail.decode bottom).tree, []⟩ 2 :=
      .step .downRight (.step .rotateRightChild .refl)
    have first := join.inContext (by intro h; cases h) (by intro h; cases h)
      [.right a.tree, .right crumb.tree]
    have second := (ih (.node b c)).inContext (by intro h; cases h)
      (push_ne_nil tail (.node b c) bottom) [.right a.tree, .right crumb.tree]
    have linked := first.append second
    convert linked using 1 <;> (try rfl)
    simp only [Layers.pushCost, List.length_cons, List.length_nil]
    omega

/-- Every borrow first exposes a next-level crumb, then right-rotates it into
two current-level crumbs. The popped separator remains at the returned root. -/
theorem pop_trace {layers rest : Layers} {crumb : WeightedTree}
    (popped : layers.pop = some (crumb, rest)) (bottom : WeightedTree) :
    Pointer.Trace ⟨(layers.decode bottom).tree, []⟩
      ⟨.node crumb.tree (rest.decode bottom).tree, []⟩ layers.popCost := by
  induction layers generalizing crumb rest with
  | nil => cases popped
  | one a tail ih =>
    by_cases empty : tail = .nil
    · subst tail
      simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
      rcases popped with ⟨rfl, rfl⟩
      exact .refl
    · rw [pop_one a empty] at popped
      cases result : tail.pop with
      | none => simp only [result] at popped; cases popped
      | some pair =>
        rcases pair with ⟨block, suffix⟩
        cases block with
        | leaf => simp only [result] at popped; cases popped
        | node b c =>
          simp only [result, Option.some.injEq, Prod.mk.injEq] at popped
          rcases popped with ⟨rfl, rfl⟩
          have first := (ih result).inContext (decode_ne_nil empty bottom)
            (by intro h; cases h) [.right a.tree]
          have split : Pointer.Trace
              ⟨.node (.node b.tree c.tree) (suffix.decode bottom).tree, []⟩
              ⟨.node b.tree (.node c.tree (suffix.decode bottom).tree), []⟩ 2 :=
            .step .downLeft (.step .rotateLeftChild .refl)
          have second := split.inContext (by intro h; cases h) (by intro h; cases h) [.right a.tree]
          have linked := first.append second
          rw [popCost_one a empty]
          convert linked using 1 <;> (try rfl)
          simp only [List.length_cons, List.length_nil]
          omega
  | two a b tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    exact .refl
  | three a b c tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    exact .refl

end RotationBST.PopTart.Cherry
