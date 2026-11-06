module

public import RotationBST.Structures.HeavyPath.Recursive.Construction
public import RotationBST.Structures.HeavyPath.Paired.Substitution.Transport
public import RotationBST.Models.Labelled.Abstract
public import RotationBST.Models.Pointer.Reshape
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive
open Paired LabelledCursor

/-- Recursive payload replacement and each paired path preserve all nodes. -/
theorem layout_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree}
    (layout : Layout weight t shape) : shape.size = t.erase.size := by
  induction layout with
  | nil => rfl
  | @path t payload positive nonempty terminal children ih =>
    obtain ⟨endpoint, focus⟩ := terminal
    have size := buildWith_size weight payload (extract weight t).context Stacks.empty
      (.node .nil endpoint .nil) rfl ih
    rw [← focus] at size
    change _ = (extract weight t).tree.erase.size at size
    simpa only [HeavyPath.Results.extract_tree] using size

theorem rebuild_size {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) : (rebuild weight t).size = t.erase.size :=
  layout_size (rebuild_layout positive)

/-- The initial recursively represented tree has precisely the original
ordered key list. The theorem does not assume that equal shapes have equal
analysis weights or identify repeated fringe shapes with one another. -/
theorem rebuild_labels {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (ordered : t.Ordered) :
    ∃! u : LabelledTree α, u.erase = rebuild weight t ∧ u.inorder = t.inorder ∧ u.Ordered := by
  apply Representation.ordered_labels_exist_unique
  · rw [Representation.Bridge.inorder_length, rebuild_size positive]
  · exact (Representation.ordered_iff t).mp ordered

/-- The generic reshape theorem supplies a linear-cost initialization on the
original node set. This is separate from the ongoing simulation operations. -/
theorem rebuild_initialization {α : Type} {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) :
    ∃ cost, cost ≤ 16 * t.erase.size ∧ Pointer.Trace ⟨t.erase, []⟩ ⟨rebuild weight t, []⟩ cost := by
  obtain ⟨cost, bound, trace⟩ := Pointer.reshape t.erase (rebuild weight t) (rebuild_size positive).symm
  exact ⟨cost, bound, trace⟩

end RotationBST.HeavyPath.Recursive
