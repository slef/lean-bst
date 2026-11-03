module

public import RotationBST.Models.Region.Basic

@[expose] public section
namespace RotationBST.Arboral.Region
open Pointer.Lazy.Skeleton

private def canonical : List Tree → Region
  | [] => .hole .nil
  | [t] => .hole t
  | t :: u :: ts => .node (.hole t) (canonical (u :: ts))

private theorem canonical_join (xs ys : List Tree) (lo : Nat)
    (hx : xs ≠ []) (hy : ys ≠ []) :
    Same (.node (canonical xs) (canonical ys)) (canonical (xs ++ ys)) lo := by
  induction xs generalizing lo with
  | nil => exact (hx rfl).elim
  | cons x xs ih =>
    cases xs with
    | nil => cases ys with
      | nil => exact (hy rfl).elim
      | cons y ys => exact Same.refl _ _
    | cons z zs =>
      have hrot := same_right (.hole x) (canonical (z :: zs)) (canonical ys) lo
      have hjoin := ih (lo + x.size + 1) (by simp)
      exact hrot.trans (same_node (Same.refl _ _) hjoin)

private theorem canonical_same (s : Region) (lo : Nat) :
    Same s (canonical s.fringe) lo := by
  induction s generalizing lo with
  | hole t => exact Same.refl _ _
  | node l r il ir =>
    have hl : l.fringe ≠ [] := by have := fringe_length l; intro he; rw [he] at this; simp at this
    have hr : r.fringe ≠ [] := by have := fringe_length r; intro he; rw [he] at this; simp at this
    exact (same_node (il lo) (ir (lo + l.tree.size + 1))).trans
      (canonical_join l.fringe r.fringe lo hl hr)

/-- The inorder fringe determines the active ranks and every hole's offset.
Thus the usual BST-model fringe condition is sufficient for `Same`. -/
theorem same_of_fringe {s t : Region} (h : s.fringe = t.fringe) (lo : Nat) : Same s t lo := by
  have hs := canonical_same s lo
  have ht := canonical_same t lo
  rw [← h] at ht
  exact hs.trans ⟨ht.1.symm, ht.2.1.symm, ht.2.2.symm⟩

end RotationBST.Arboral.Region
