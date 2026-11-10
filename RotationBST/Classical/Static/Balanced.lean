module

public import RotationBST.Models.Rotation.Shapes
public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import RotationBST.Bounds.Logarithmic.Abstract
public import RotationBST.Bounds.Implications.LogSum
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Depth facts about the balanced tree and about arbitrary trees. -/
namespace RotationBST.Classical.Static
open _root_.RotationBST.Tree (balanced)

theorem balanced_depth (n x : Nat) (hx : x < n) : (balanced n).depth x ≤ Nat.log2 n := by
  have := Tree.depth_lt_height (balanced n) x (by rwa [Tree.balanced_size])
  have := Tree.balanced_height n
  omega

/-- Every nonempty tree has a key whose depth `d` satisfies `size < 2^(d+1)`. -/
theorem exists_deep_pow (t : Tree) (h : 0 < t.size) :
    ∃ x < t.size, t.size < 2 ^ (t.depth x + 1) := by
  induction t with
  | nil => simp [Tree.size] at h
  | node l r ihl ihr =>
    by_cases hlr : r.size ≤ l.size
    · by_cases hl : l.size = 0
      · refine ⟨0, by simp only [Tree.size]; omega, ?_⟩
        have hr : r.size = 0 := by omega
        simp [Tree.depth, Tree.size, hl, hr]
      · obtain ⟨y, hy, hd⟩ := ihl (by omega)
        refine ⟨y, by simp [Tree.size]; omega, ?_⟩
        simp only [Tree.depth, hy, ↓reduceIte, Tree.size]
        have power : 2 ^ (l.depth y + 1 + 1) = 2 ^ (l.depth y + 1) * 2 := Nat.pow_succ ..
        omega
    · obtain ⟨y, hy, hd⟩ := ihr (by omega)
      refine ⟨l.size + 1 + y, by simp [Tree.size]; omega, ?_⟩
      have e : l.size + 1 + y - l.size - 1 = y := by omega
      have h₁ : ¬ l.size + 1 + y < l.size := by omega
      have h₂ : l.size + 1 + y ≠ l.size := by omega
      simp only [Tree.depth, h₁, h₂, ↓reduceIte, e, Tree.size]
      have power : 2 ^ (r.depth y + 1 + 1) = 2 ^ (r.depth y + 1) * 2 := Nat.pow_succ ..
      omega

theorem exists_deep (t : Tree) (h : 0 < t.size) :
    ∃ x < t.size, Nat.log2 t.size ≤ t.depth x := by
  obtain ⟨x, hx, hd⟩ := exists_deep_pow t h
  exact ⟨x, hx, Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).mpr hd)⟩

theorem cost_le_of_depth_le (t : Tree) (d : Nat) (xs : List Nat)
    (hd : ∀ x ∈ xs, t.depth x ≤ d) : StaticTree.cost t xs ≤ xs.length * (d + 1) := by
  induction xs with
  | nil => simp [StaticTree.cost]
  | cons x xs ih =>
    have hx := hd x (by simp)
    have := ih (fun y hy => hd y (by simp [hy]))
    simp only [StaticTree.cost, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    rw [Nat.succ_mul]
    omega

theorem balanced_cost (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    StaticTree.cost (balanced n) xs ≤ xs.length * (Nat.log2 n + 1) :=
  cost_le_of_depth_le _ _ xs fun x hx => balanced_depth n x (valid x hx)

theorem cost_replicate (t : Tree) (m x : Nat) :
    StaticTree.cost t (List.replicate m x) = m * (t.depth x + 1) := by
  induction m with
  | zero => simp [StaticTree.cost]
  | succ m ih =>
    simp only [StaticTree.cost, List.replicate_succ, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Nat.succ_mul]
    omega

/-- Repeating a deepest key costs every static tree `m(1 + ⌊log₂ n⌋)`. -/
theorem exists_expensive (t : Tree) (h : 0 < t.size) (m : Nat) :
    ∃ x < t.size, m * (Nat.log2 t.size + 1) ≤ StaticTree.cost t (List.replicate m x) := by
  obtain ⟨x, hx, hd⟩ := exists_deep t h
  exact ⟨x, hx, by rw [cost_replicate]; exact Nat.mul_le_mul_left m (by omega)⟩

/-- The balanced tree meets the logarithmic baseline with constant one. -/
theorem balanced_cost_le_logCost (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    (StaticTree.cost (balanced n) xs : ℝ) ≤ Bounds.logCost n xs := by
  have hc : (StaticTree.cost (balanced n) xs : ℝ) ≤ (xs.length : ℝ) * (Nat.log2 n + 1) := by
    exact_mod_cast balanced_cost n xs valid
  unfold Bounds.logCost
  by_cases hn : n = 0
  · subst hn
    have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => have := valid x (by simp); omega
    subst hxs
    simp at hc ⊢
    exact_mod_cast hc
  · have hl := Bounds.le_logb_of_pow _ _ (Nat.log2_self_le hn)
    have hm := mul_le_mul_of_nonneg_left (show (Nat.log2 n : ℝ) + 1 ≤ 1 + Real.logb 2 n by linarith)
      (Nat.cast_nonneg (α := ℝ) xs.length)
    linarith

end RotationBST.Classical.Static
