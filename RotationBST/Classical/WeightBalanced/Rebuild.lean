module

public import RotationBST.Classical.WeightBalanced.Definitions.Abstract
public import RotationBST.Models.Rotation.Shapes
public import RotationBST.Models.Rotation.Connectivity.Proofs
import Mathlib.Tactic

@[expose] public section

/-! Rebuilding: to the right spine in `vineCost` rotations, then back from the
spine to the balanced tree, at most `2n` rotations in all. -/
namespace RotationBST.Classical.WeightBalanced
open _root_.RotationBST.Tree (balanced)

theorem vineCost_le (t : Tree) : vineCost t ≤ t.size := by
  induction t with
  | nil => simp [vineCost]
  | node l r _ ir => simp only [vineCost, Tree.size]; omega

/-- The vine procedure uses exactly `vineCost` rotations. -/
theorem vine_rotations (t : Tree) : Rotations t (spine t.size .nil) (vineCost t) := by
  induction t with
  | nil => exact .refl
  | node l r _ ir =>
      have first := promote_left l r
      have second := (ir.inRight (l := Tree.nil)).inSpine l.size
      have result := first.append second
      simpa only [Tree.size, Nat.add_assoc, spine_add, spine, vineCost] using result

theorem rebuild_size (t : Tree) : (rebuild t).1.size = t.size := Tree.balanced_size _

theorem rebuild_rotations (t : Tree) : Rotations t (rebuild t).1 (rebuild t).2 := by
  have h1 := vine_rotations t
  have h2 := (vine_rotations (balanced t.size)).symm
  rw [Tree.balanced_size] at h2
  exact h1.append h2

theorem rebuild_cost (t : Tree) : (rebuild t).2 ≤ 2 * t.size := by
  have := vineCost_le t
  have := vineCost_le (balanced t.size)
  rw [Tree.balanced_size] at this
  simp only [rebuild]; omega

end RotationBST.Classical.WeightBalanced
