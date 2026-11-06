module

public import RotationBST.Structures.HeavyPath.Extraction
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath
open LabelledCursor

private theorem ordered_focus {α : Type} [LT α] (cs : List (Frame α)) (t : LabelledTree α)
    (ordered : (plug cs t).Ordered) : t.Ordered := by
  induction cs generalizing t with
  | nil => exact ordered
  | cons frame cs ih =>
    cases frame with
    | left x r => exact (ih (.node t x r) ordered).1
    | right l x => exact (ih (.node l x t) ordered).2.1

/-- The two path subsequences have the orientations required by the two
oppositely oriented pop-tarts. Bounds hold for every key in the focus subtree. -/
theorem context_order {α : Type} [LT α] (cs : List (Frame α)) (t : LabelledTree α)
    (ordered : (plug cs t).Ordered) :
    (lowerKeys cs).Pairwise (fun a b => b < a) ∧ (upperKeys cs).Pairwise (fun a b => a < b) ∧
      ∀ y ∈ t.inorder, (∀ x ∈ lowerKeys cs, x < y) ∧ (∀ x ∈ upperKeys cs, y < x) := by
  induction cs generalizing t with
  | nil => simp [lowerKeys, upperKeys]
  | cons frame cs ih =>
    cases frame with
    | left x r =>
      have parentOrdered := ordered_focus cs (.node t x r) ordered
      obtain ⟨lower, upper, bounds⟩ := ih (.node t x r) ordered
      simp only [lowerKeys, upperKeys]
      refine ⟨lower, List.pairwise_cons.mpr ⟨?_, upper⟩, ?_⟩
      · exact (bounds x (by simp [LabelledTree.inorder])).2
      · intro y mem
        have ancestor := bounds y (by simp [LabelledTree.inorder, mem])
        refine ⟨ancestor.1, ?_⟩
        intro z member
        rcases List.mem_cons.mp member with rfl | member
        · exact parentOrdered.2.2.1 y mem
        · exact ancestor.2 z member
    | right l x =>
      have parentOrdered := ordered_focus cs (.node l x t) ordered
      obtain ⟨lower, upper, bounds⟩ := ih (.node l x t) ordered
      simp only [lowerKeys, upperKeys]
      refine ⟨List.pairwise_cons.mpr ⟨?_, lower⟩, upper, ?_⟩
      · exact (bounds x (by simp [LabelledTree.inorder])).1
      · intro y mem
        have ancestor := bounds y (by simp [LabelledTree.inorder, mem])
        refine ⟨?_, ancestor.2⟩
        intro z member
        rcases List.mem_cons.mp member with rfl | member
        · exact parentOrdered.2.2.2 y mem
        · exact ancestor.1 z member

/-- Canonical extraction supplies both monotone separator subsequences while
retaining all the off-path subtrees in the same labelled frames. -/
theorem extract_order {α : Type} [LT α] (weight : α → ℝ) {t : LabelledTree α} (ordered : t.Ordered) :
    (lowerKeys (extract weight t).context).Pairwise (fun a b => b < a) ∧
      (upperKeys (extract weight t).context).Pairwise (fun a b => a < b) ∧
      ∀ y ∈ (extract weight t).focus.inorder,
        (∀ x ∈ lowerKeys (extract weight t).context, x < y) ∧
        (∀ x ∈ upperKeys (extract weight t).context, y < x) := by
  apply context_order
  change (extract weight t).tree.Ordered
  rw [extract_tree]
  exact ordered

end RotationBST.HeavyPath
