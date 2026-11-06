module

public import RotationBST.Structures.HeavyPath.Recursive.History.Entries
public import RotationBST.Structures.HeavyPath.Recursive.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History
open Paired LabelledCursor PopTart PopTart.WeightedTree

theorem path_size {α : Type} {weight : α → ℝ} {es : List (Entry α)} {p : Stacks} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil)
    (context : es.map Entry.source = (extract weight t).context) (valid : PathValid weight es p)
    (sizes : ∀ e ∈ es, e.shape.size = (framePayload e.source).erase.size) : p.tree.size = t.erase.size := by
  obtain ⟨endpoint, focus⟩ := HeavyPath.Results.extract_terminal positive nonempty
  have lowerSizes : ∀ e ∈ lower es, (Entry.lowerBlock e).length = e.shape.size + 1 := by
    intro e member
    rw [Entry.lowerBlock, (block_length e.source).1, sizes e (lower_mem member)]
  have upperSizes : ∀ e ∈ upper es, (Entry.upperBlock e).length = e.shape.size + 1 := by
    intro e member
    rw [Entry.upperBlock, (block_length e.source).2, sizes e (upper_mem member)]
  have l := fringeSpan_fringe p.lower.decode
  have r := fringeSpan_fringe p.upper.decode.mirror
  rw [valid.lower, fringeSpan_append, blocks_span weight Entry.lowerBlock _ lowerSizes] at l
  rw [valid.upper, fringeSpan_append, blocks_span weight Entry.upperBlock _ upperSizes] at r
  have inorder := congrArg List.length (entries_inorder context focus)
  simp only [List.length_append, List.length_singleton, Representation.Bridge.inorder_length] at inorder
  simp only [fringeSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Tree.size, Nat.zero_add, Nat.add_zero, mirror_tree, Tree.mirror_size] at l r
  simp only [Stacks.tree, Tree.size, Tree.mirror_size]
  omega

theorem layout_positive {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) : Positive weight t := by
  cases layout with
  | nil => trivial
  | path positive => exact positive

theorem layout_size {α : Type} {weight : α → ℝ} {t : LabelledTree α} {shape : Tree} {credit : Nat}
    (layout : Layout weight t shape credit) : shape.size = t.erase.size := by
  induction layout with
  | nil => rfl
  | path positive nonempty context valid children ih => exact path_size positive nonempty context valid ih

/-- Ordered labels are inherited by rank for every supported history. -/
theorem layout_labels {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    {shape : Tree} {credit : Nat} (layout : Layout weight t shape credit) (ordered : t.Ordered) :
    ∃! u : LabelledTree α, u.erase = shape ∧ u.inorder = t.inorder ∧ u.Ordered := by
  apply Representation.ordered_labels_exist_unique
  · rw [Representation.Bridge.inorder_length, layout_size layout]
  · exact (Representation.ordered_iff t).mp ordered

end RotationBST.HeavyPath.Recursive.History
