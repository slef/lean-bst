module

public import RotationBST.Structures.PopTart.Cherry.Definitions.Abstract
public import RotationBST.Structures.PopTart.Height
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.Cherry
open WeightedTree

theorem pop_one (a : WeightedTree) {tail : Layers} (nonempty : tail ≠ .nil) :
    (Layers.one a tail).pop = match tail.pop with
      | some (.node b c, rest) => some (a, .two b c rest)
      | _ => none := by
  cases tail <;> first | exact False.elim (nonempty rfl) | rfl

theorem popCost_one (a : WeightedTree) {tail : Layers} (nonempty : tail ≠ .nil) :
    (Layers.one a tail).popCost = 6 + tail.popCost := by
  cases tail <;> first | exact False.elim (nonempty rfl) | rfl

theorem push_valid {level : Nat} {layers : Layers} (valid : Valid level layers)
    {crumb : WeightedTree} (perfect : Perfect level crumb) : Valid level (layers.push crumb) := by
  induction valid generalizing crumb with
  | nil => exact .one perfect (.nil _)
  | one a tail ih => exact .two perfect a tail
  | two a b tail ih => exact .three perfect a b tail
  | three a b c tail ih => exact .two perfect a (ih (.node b c))

/-- Every nonempty valid layer stack pops successfully and returns a perfect
crumb of its original level, with the remaining layers still valid. -/
theorem pop_valid {level : Nat} {layers : Layers} (valid : Valid level layers) (nonempty : layers ≠ .nil) :
    ∃ crumb rest, layers.pop = some (crumb, rest) ∧ Perfect level crumb ∧ Valid level rest := by
  induction valid with
  | nil => exact False.elim (nonempty rfl)
  | @one level a tail pa vt ih =>
    cases tail with
    | nil => exact ⟨a, .nil, rfl, pa, .nil _⟩
    | one b more | two b c more | three b c d more =>
      obtain ⟨crumb, rest, popped, perfect, validRest⟩ := ih (by intro h; cases h)
      cases perfect with
      | node pb pc => exact ⟨a, _, by rw [pop_one a (by intro h; cases h), popped], pa, .two pb pc validRest⟩
  | two a b tail ih => exact ⟨_, _, rfl, a, .one b tail⟩
  | three a b c tail ih => exact ⟨_, _, rfl, a, .two b c tail⟩

/-- A successful pop has exactly the valid crumb and suffix certified above. -/
theorem popped_valid {level : Nat} {layers rest : Layers} {crumb : WeightedTree}
    (valid : Valid level layers) (popped : layers.pop = some (crumb, rest)) :
    Perfect level crumb ∧ Valid level rest := by
  have nonempty : layers ≠ .nil := by intro h; subst layers; cases popped
  obtain ⟨other, tail, same, perfect, validRest⟩ := pop_valid valid nonempty
  rw [popped] at same
  cases same
  exact ⟨perfect, validRest⟩

end RotationBST.PopTart.Cherry
