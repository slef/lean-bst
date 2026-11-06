module

public import RotationBST.Structures.HeavyPath.Paired.Build
public import RotationBST.Models.Labelled.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired

/-- The physical construction also realizes labelled rotations, preserving
every key, its inorder position, and BST ordering. Its rotation count is
bounded by the same charged pointer trace. -/
theorem extract_build_labelled {α : Type} [Preorder α] {weight : α → ℝ} {t : LabelledTree α}
    (positive : Positive weight t) (nonempty : t ≠ .nil) (ordered : t.Ordered) :
    let p := Stacks.build weight (extract weight t).context Stacks.empty
    ∃ u : LabelledTree α, ∃ rotations cost,
      u.erase = p.tree ∧ u.inorder = t.inorder ∧ u.Ordered ∧
      LabelledTree.Rotations t u rotations ∧ rotations ≤ cost ∧
      Pointer.Trace ⟨t.erase, []⟩ ⟨p.tree, []⟩ cost ∧
      cost + p.potential ≤ 24 * (extract weight t).context.length := by
  dsimp only
  obtain ⟨x, cost, focus, valid, mass, trace, bound, key⟩ := extract_build positive nonempty
  obtain ⟨rotations, count, rotated⟩ := trace.rotations
  obtain ⟨u, labelled, shape⟩ := Representation.Bridge.lift_rotations rotated t rfl
  exact ⟨u, rotations, cost, shape, (Representation.Bridge.inorder_rotations labelled).symm,
    (Representation.rotations_preserve_order labelled).mp ordered, labelled, count, trace, bound⟩

end RotationBST.HeavyPath.Paired
