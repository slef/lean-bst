module

public import RotationBST.Structures.HeavyPath.Context
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

private theorem extract_left {α : Type} {weight : α → ℝ} {l r : LabelledTree α} (x : α)
    (heavy : LeftHeavy weight l r) (nonempty : l ≠ .nil) :
    extract weight (.node l x r) = extend (extract weight l) (.left x r) := by
  classical
  simp only [extract, heavy, nonempty, ite_true, ite_false]

private theorem extract_right {α : Type} {weight : α → ℝ} {l r : LabelledTree α} (x : α)
    (heavy : ¬ LeftHeavy weight l r) (nonempty : r ≠ .nil) :
    extract weight (.node l x r) = extend (extract weight r) (.right l x) := by
  classical
  simp only [extract, heavy, nonempty, ite_false]

/-- Extraction preserves the entire labelled tree, not only its key set. -/
theorem extract_tree {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    (extract weight t).tree = t := by
  classical
  induction t with
  | nil => rfl
  | node l x r ihL ihR =>
    by_cases heavy : LeftHeavy weight l r
    · by_cases empty : l = .nil
      · subst l
        simp only [extract, heavy, ite_true, Config.tree, plug]
      · rw [extract_left x heavy empty, extend_left_tree, ihL]
    · by_cases empty : r = .nil
      · subst r
        simp only [extract, heavy, ite_false, ite_true, Config.tree, plug]
      · rw [extract_right x heavy empty, extend_right_tree, ihR]

theorem extract_nonempty {α : Type} (weight : α → ℝ) {t : LabelledTree α} (nonempty : t ≠ .nil) :
    (extract weight t).focus ≠ .nil := by
  classical
  induction t with
  | nil => exact False.elim (nonempty rfl)
  | node l x r ihL ihR =>
    by_cases heavy : LeftHeavy weight l r
    · by_cases empty : l = .nil
      · subst l
        simp only [extract, heavy, ite_true]; intro h; cases h
      · rw [extract_left x heavy empty]
        exact ihL empty
    · by_cases empty : r = .nil
      · subst r
        simp only [extract, heavy, ite_false, ite_true]; intro h; cases h
      · rw [extract_right x heavy empty]
        exact ihR empty

/-- Every frame of the extracted path selects the canonical solid edge. -/
theorem extract_solid {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    SolidContext weight (extract weight t).focus (extract weight t).context := by
  classical
  induction t with
  | nil => trivial
  | node l x r ihL ihR =>
    by_cases heavy : LeftHeavy weight l r
    · by_cases empty : l = .nil
      · subst l
        simp only [extract, heavy, ite_true, SolidContext]
      · rw [extract_left x heavy empty]
        change SolidContext weight (extract weight l).focus ((extract weight l).context ++ [.left x r])
        rw [solid_append]
        refine ⟨ihL, ?_⟩
        change LeftHeavy weight (extract weight l).tree r ∧ True
        rw [extract_tree]
        exact ⟨heavy, trivial⟩
    · by_cases empty : r = .nil
      · subst r
        simp only [extract, heavy, ite_false, ite_true, SolidContext]
      · rw [extract_right x heavy empty]
        change SolidContext weight (extract weight r).focus ((extract weight r).context ++ [.right l x])
        rw [solid_append]
        refine ⟨ihR, ?_⟩
        change (¬ LeftHeavy weight l (extract weight r).tree) ∧ True
        rw [extract_tree]
        exact ⟨heavy, trivial⟩

/-- With positive node weights the maximal solid path ends at a leaf node. -/
theorem extract_terminal {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) :
    ∃ x, (extract weight t).focus = .node .nil x .nil := by
  classical
  induction t with
  | nil => exact False.elim (nonempty rfl)
  | node l x r ihL ihR =>
    by_cases heavy : LeftHeavy weight l r
    · by_cases empty : l = .nil
      · have rightEmpty : r = .nil := by
          by_contra hn
          have rightPositive := mass_positive positive.2.2 hn
          change mass weight r ≤ mass weight l at heavy
          rw [empty, mass] at heavy
          linarith only [heavy, rightPositive]
        subst l
        subst r
        exact ⟨x, by simp [extract, LeftHeavy, mass]⟩
      · rw [extract_left x heavy empty]
        exact ihL positive.1 empty
    · by_cases empty : r = .nil
      · have leftMass := mass_nonnegative (positive_nonnegative positive.1)
        change ¬ mass weight r ≤ mass weight l at heavy
        rw [empty, mass] at heavy
        exact False.elim (heavy leftMass)
      · rw [extract_right x heavy empty]
        exact ihR positive.2.2 empty

/-- Endpoint mass and frame charges partition all original node weights. -/
theorem extract_mass {α : Type} (weight : α → ℝ) (t : LabelledTree α) :
    mass weight t = mass weight (extract weight t).focus +
      ((extract weight t).context.map (frameMass weight)).sum := by
  have result := context_mass weight (extract weight t).context (extract weight t).focus
  change mass weight (extract weight t).tree = _ at result
  rw [extract_tree] at result
  exact result

/-- The extracted endpoint is reached by an actual pointer descent through
exactly the recorded number of solid edges. -/
theorem extract_trace {α : Type} (weight : α → ℝ) {t : LabelledTree α} (nonempty : t ≠ .nil) :
    Pointer.Trace ⟨t.erase, []⟩ (extract weight t).erase (extract weight t).context.length := by
  simpa only [extract_tree] using cursor_trace (extract weight t) (extract_nonempty weight nonempty)

end RotationBST.HeavyPath
