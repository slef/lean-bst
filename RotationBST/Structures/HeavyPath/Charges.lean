module

public import RotationBST.Structures.HeavyPath.Extraction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

/-- Positive original node weights give a positive endpoint and positive
frame charges, even when the off-path subtrees are empty. -/
theorem context_positive {α : Type} {weight : α → ℝ} (cs : List (Frame α)) (t : LabelledTree α)
    (positive : Positive weight (plug cs t)) :
    Positive weight t ∧ ∀ frame ∈ cs, 0 < frameMass weight frame := by
  induction cs generalizing t with
  | nil => exact ⟨positive, by simp⟩
  | cons frame cs ih =>
    cases frame with
    | left x r =>
      obtain ⟨parent, rest⟩ := ih (.node t x r) positive
      refine ⟨parent.1, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · have light := mass_nonnegative (positive_nonnegative parent.2.2)
        exact add_pos_of_pos_of_nonneg parent.2.1 light
      · exact rest frame member
    | right l x =>
      obtain ⟨parent, rest⟩ := ih (.node l x t) positive
      refine ⟨parent.2.2, ?_⟩
      intro frame member
      rcases List.mem_cons.mp member with rfl | member
      · have light := mass_nonnegative (positive_nonnegative parent.1)
        exact add_pos_of_nonneg_of_pos light parent.2.1
      · exact rest frame member

theorem extract_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α} (positive : Positive weight t) :
    Positive weight (extract weight t).focus ∧
      ∀ frame ∈ (extract weight t).context, 0 < frameMass weight frame := by
  apply context_positive
  change Positive weight (extract weight t).tree
  rw [extract_tree]
  exact positive

end RotationBST.HeavyPath
