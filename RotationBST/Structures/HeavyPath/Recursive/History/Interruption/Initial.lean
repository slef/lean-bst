module

public import RotationBST.Structures.HeavyPath.Recursive.History.Depth
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Recursive.History.Interruption

private theorem log_mono_mass {small large key : ℝ} (positive : 0 < key)
    (keyMass : key ≤ small) (total : small ≤ large) :
    Real.logb 2 (small / key) ≤ Real.logb 2 (large / key) := by
  apply Real.logb_le_logb_of_le (by norm_num) (div_pos (lt_of_lt_of_le positive keyMass) positive)
  exact div_le_div_of_nonneg_right total positive.le

/-- Before joining, the root and its two arbitrary recursive layouts already
have a weighted depth bound with the mass of the entire source subtree. -/
theorem node_depth_at {α : Type} {weight : α → ℝ} {l r : LabelledTree α} {key : α}
    {a b : Tree} {lc rc : Nat} (left : Layout weight l a lc) (right : Layout weight r b rc)
    (positive : 0 < weight key) (rank : Fin (LabelledTree.node l key r).inorder.length) :
    (Tree.depth (.node a b) rank.val : ℝ) ≤
      8 + 15 * Real.logb 2 (mass weight (.node l key r) /
        weight ((LabelledTree.node l key r).inorder[rank.val]'rank.isLt)) := by
  have leftNonnegative := mass_nonnegative (positive_nonnegative (layout_positive left))
  have rightNonnegative := mass_nonnegative (positive_nonnegative (layout_positive right))
  have leftMass : mass weight l ≤ mass weight (.node l key r) := by simp only [mass]; linarith
  have rightMass : mass weight r ≤ mass weight (.node l key r) := by simp only [mass]; linarith
  have size : a.size = l.inorder.length := by rw [layout_size left, Representation.Bridge.inorder_length]
  have length := rank.isLt
  simp only [LabelledTree.inorder, List.length_append, List.length_cons] at length
  by_cases inside : rank.val < l.inorder.length
  · have keyEq : (LabelledTree.node l key r).inorder[rank.val] = l.inorder[rank.val] := by
      simp only [LabelledTree.inorder, List.getElem_append_left inside]
    have initial : Tree.depth (.node a b) rank.val = Tree.depth a rank.val + 1 := by
      rw [Tree.depth, ite_eq_left (by omega)]
    obtain ⟨keyPositive, keyMass⟩ := inorder_weight (layout_positive left) (List.getElem_mem inside)
    have logarithm := log_mono_mass keyPositive keyMass leftMass
    have child := layout_depth_at left ⟨rank.val, inside⟩
    rw [initial, keyEq, Nat.cast_add, Nat.cast_one]
    linarith
  · by_cases atRoot : rank.val = l.inorder.length
    · have keyEq : (LabelledTree.node l key r).inorder[rank.val] = key := by
        simp only [LabelledTree.inorder, atRoot]
        rw [List.getElem_append_right (as := l.inorder) (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem_cons_zero]
      have initial : Tree.depth (.node a b) rank.val = 0 := by
        simp [Tree.depth, size, atRoot]
      have logarithm : 0 ≤ Real.logb 2 (mass weight (.node l key r) / weight key) := by
        apply Real.logb_nonneg (by norm_num)
        apply (le_div_iff₀ positive).mpr
        simp only [one_mul, mass]
        linarith
      rw [initial, keyEq]
      norm_num only [Nat.cast_zero]
      linarith
    · have inRight : rank.val - l.inorder.length - 1 < r.inorder.length := by omega
      have keyEq : (LabelledTree.node l key r).inorder[rank.val] =
          r.inorder[rank.val - l.inorder.length - 1] := by
        simp only [LabelledTree.inorder]
        rw [List.getElem_append_right (as := l.inorder) (i := rank.val) (by omega)]
        rw [List.getElem_cons]
        split
        · omega
        · rfl
      have initial : Tree.depth (.node a b) rank.val =
          Tree.depth b (rank.val - l.inorder.length - 1) + 1 := by
        rw [Tree.depth, ite_eq_right (by omega), ite_eq_right (by omega), size]
      obtain ⟨keyPositive, keyMass⟩ := inorder_weight (layout_positive right) (List.getElem_mem inRight)
      have logarithm := log_mono_mass keyPositive keyMass rightMass
      have child := layout_depth_at right ⟨_, inRight⟩
      rw [initial, keyEq, Nat.cast_add, Nat.cast_one]
      linarith

end RotationBST.HeavyPath.Recursive.History.Interruption
