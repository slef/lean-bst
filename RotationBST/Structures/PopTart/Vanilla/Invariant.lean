module

public import RotationBST.Structures.PopTart.Vanilla.Definitions.Abstract
public import RotationBST.Structures.PopTart.Slots
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Vanilla

theorem nonnegative {stack : WeightedTree} (valid : Valid stack) : stack.Nonnegative := by
  induction valid with
  | leaf t w pos => exact pos
  | push t w valid dominates ih =>
    exact ⟨(WeightedTree.mass_nonnegative ih).trans dominates, ih⟩

theorem push_valid {stack : WeightedTree} (valid : Valid stack) (t : Tree) (w : ℝ)
    (dominates : stack.mass ≤ w) : Valid (push t w stack) :=
  .push t w valid dominates

theorem pop_push (t : Tree) (w : ℝ) (stack : WeightedTree) :
    pop (push t w stack) = some ((t, w), stack) := rfl

theorem pop_valid {stack tail : WeightedTree} {t : Tree} {w : ℝ}
    (valid : Valid stack) (exposed : pop stack = some ((t, w), tail)) :
    Valid tail ∧ 0 ≤ w ∧ tail.mass ≤ w := by
  cases valid with
  | leaf => simp [pop] at exposed
  | push t' w' tailValid dominates =>
    simp only [pop, Option.some.injEq, Prod.mk.injEq] at exposed
    rcases exposed with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨tailValid, (WeightedTree.mass_nonnegative (nonnegative tailValid)).trans dominates, dominates⟩

/-- The complete weighted root decomposition, including the empty stack. -/
theorem cases_valid {stack : WeightedTree} (valid : Valid stack) :
    (∃ t w, stack = .leaf t w ∧ 0 ≤ w) ∨
      ∃ t w tail, stack = push t w tail ∧ Valid tail ∧ tail.mass ≤ w := by
  cases valid with
  | leaf t w pos => exact Or.inl ⟨t, w, rfl, pos⟩
  | push t w tailValid dominates => exact Or.inr ⟨t, w, _, rfl, tailValid, dominates⟩

end RotationBST.PopTart.Vanilla
