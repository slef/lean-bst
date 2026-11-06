module

public import RotationBST.Structures.HeavyPath.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath

theorem positive_nonnegative {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) : Nonnegative weight t := by
  induction t with
  | nil => trivial
  | node l x r ihL ihR => exact ⟨ihL positive.1, positive.2.1.le, ihR positive.2.2⟩

theorem mass_nonnegative {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (nonnegative : Nonnegative weight t) : 0 ≤ mass weight t := by
  induction t with
  | nil => exact le_rfl
  | node l x r ihL ihR =>
    exact add_nonneg (add_nonneg (ihL nonnegative.1) nonnegative.2.1) (ihR nonnegative.2.2)

theorem mass_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) : 0 < mass weight t := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | node l x r =>
    have left := mass_nonnegative (positive_nonnegative positive.1)
    have right := mass_nonnegative (positive_nonnegative positive.2.2)
    change 0 < mass weight l + weight x + mass weight r
    linarith only [left, positive.2.1, right]

/-- The dotted right edge loses at least half the total parent mass. -/
theorem right_light_half {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (nonnegative : Nonnegative weight (.node l x r)) (heavy : LeftHeavy weight l r) :
    2 * mass weight r ≤ mass weight (.node l x r) := by
  change mass weight r ≤ mass weight l at heavy
  change 2 * mass weight r ≤ mass weight l + weight x + mass weight r
  linarith only [heavy, nonnegative.2.1]

/-- When the right child is heavy, the dotted left edge also halves mass. -/
theorem left_light_half {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {x : α}
    (nonnegative : Nonnegative weight (.node l x r)) (heavy : ¬ LeftHeavy weight l r) :
    2 * mass weight l ≤ mass weight (.node l x r) := by
  change ¬ mass weight r ≤ mass weight l at heavy
  change 2 * mass weight l ≤ mass weight l + weight x + mass weight r
  linarith only [heavy, nonnegative.2.1]

theorem unit_positive {α : Type} (t : LabelledTree α) : Positive (fun _ => 1) t := by
  induction t <;> simp_all [Positive]

theorem unit_mass {α : Type} (t : LabelledTree α) : mass (fun _ => 1) t = (t.erase.size : ℝ) := by
  induction t <;> simp_all [mass, LabelledTree.erase, Tree.size, Nat.cast_add, Nat.cast_one]

end RotationBST.HeavyPath
