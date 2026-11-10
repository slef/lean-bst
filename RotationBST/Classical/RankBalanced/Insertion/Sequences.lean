module

public import RotationBST.Classical.RankBalanced.Insertion.Validity
import Mathlib.Tactic

@[expose] public section

/-! Sequences of insertions from the empty tree keep the AVL rule. -/
namespace RotationBST.Classical.RankBalanced

theorem insertAll_avl (t : RankedTree) (gs : List Nat) (h : Valid .avl t) : Valid .avl (insertAll t gs) := by
  induction gs generalizing t with
  | nil => exact h
  | cons g gs ih => exact ih _ (insert_avl t g h)

theorem insertAll_size (t : RankedTree) (gs : List Nat) :
    (insertAll t gs).erase.size = t.erase.size + gs.length := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih => simp only [insertAll, ih, insert_size, List.length_cons]; omega

/-- After `m` insertions into the empty tree, the height is at most `log_φ(m + 1)`. -/
theorem insertAll_height (gs : List Nat) :
    (Static.height (insertAll .nil gs).erase : ℝ) ≤ Real.logb Real.goldenRatio (gs.length + 1) := by
  have := avl_height _ (insertAll_avl .nil gs trivial)
  rw [insertAll_size] at this
  simpa [LabelledTree.erase, Tree.size] using this

end RotationBST.Classical.RankBalanced
