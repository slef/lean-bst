module

public import RotationBST.Structures.PopTart.Cherry.Invariant
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry

/-- Carries preserve the entire weighted inorder fringe, not just its size. -/
theorem push_fringe (layers : Layers) (crumb bottom : WeightedTree) :
    ((layers.push crumb).decode bottom).fringe = crumb.fringe ++ (layers.decode bottom).fringe := by
  induction layers generalizing crumb with
  | nil => rfl
  | one a tail ih => rfl
  | two a b tail ih => rfl
  | three a b c tail ih =>
    simp only [Layers.push, Layers.decode, WeightedTree.fringe, ih, List.append_assoc]

/-- Borrowing returns precisely the first weighted crumb and retains the
remaining fringe in its original order. -/
theorem pop_fringe {layers rest : Layers} {crumb : WeightedTree}
    (popped : layers.pop = some (crumb, rest)) (bottom : WeightedTree) :
    (layers.decode bottom).fringe = crumb.fringe ++ (rest.decode bottom).fringe := by
  induction layers generalizing crumb rest with
  | nil => cases popped
  | one a tail ih =>
    by_cases empty : tail = .nil
    · subst tail
      simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
      rcases popped with ⟨rfl, rfl⟩
      rfl
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
          have retained := ih result
          simp only [Layers.decode, WeightedTree.fringe, retained, List.append_assoc]
  | two a b tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    rfl
  | three a b c tail ih =>
    simp only [Layers.pop, Option.some.injEq, Prod.mk.injEq] at popped
    rcases popped with ⟨rfl, rfl⟩
    rfl

end RotationBST.PopTart.Cherry
