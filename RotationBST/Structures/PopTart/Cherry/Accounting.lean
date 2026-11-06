module

public import RotationBST.Structures.PopTart.Cherry.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

theorem push_amortized (layers : Layers) (crumb : WeightedTree) :
    layers.pushCost + (layers.push crumb).potential ≤ 10 + layers.potential := by
  induction layers generalizing crumb with
  | nil => simp [Layers.pushCost, Layers.push, Layers.potential]
  | one a tail ih => simp only [Layers.pushCost, Layers.push, Layers.potential]; omega
  | two a b tail ih => simp [Layers.pushCost, Layers.push, Layers.potential]
  | three a b c tail ih =>
    have bound := ih (.node b c)
    simp only [Layers.pushCost, Layers.push, Layers.potential]
    omega

theorem pop_amortized {layers rest : Layers} {crumb : WeightedTree}
    (popped : layers.pop = some (crumb, rest)) :
    layers.popCost + rest.potential ≤ 10 + layers.potential := by
  induction layers generalizing crumb rest with
  | nil => cases popped
  | one a tail ih =>
    by_cases empty : tail = .nil
    · subst tail
      simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
      rcases popped with ⟨rfl, rfl⟩
      simp [Layers.popCost, Layers.potential]
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
          have bound := ih result
          rw [popCost_one a empty]
          simp only [Layers.potential]
          omega
  | two a b tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    simp [Layers.popCost, Layers.potential]
  | three a b c tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    simp only [Layers.popCost, Layers.potential]
    omega

theorem push_cost_height (layers : Layers) : layers.pushCost ≤ 10 * layers.height := by
  induction layers <;> simp_all [Layers.pushCost, Layers.height]; omega

theorem pop_cost_height (layers : Layers) : layers.popCost ≤ 6 * layers.height := by
  induction layers with
  | nil => simp [Layers.popCost, Layers.height]
  | one a tail ih =>
    by_cases empty : tail = .nil
    · subst tail; simp [Layers.popCost, Layers.height]
    · rw [popCost_one a empty]
      simp only [Layers.height]
      omega
  | two a b tail ih => simp [Layers.popCost, Layers.height]
  | three a b c tail ih => simp [Layers.popCost, Layers.height]

end RotationBST.PopTart.Cherry
