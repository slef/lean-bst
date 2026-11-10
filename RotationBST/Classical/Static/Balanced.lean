module

public import RotationBST.Classical.Static.Definitions.Abstract
public import RotationBST.Bounds.StaticTree.Definitions.Abstract
public import RotationBST.Bounds.Logarithmic.Abstract
import Mathlib.Data.Nat.Init
import Mathlib.Tactic.SplitIfs

@[expose] public section

/-! Depth facts about the balanced tree and about arbitrary trees. -/
namespace RotationBST.Classical.Static

theorem balanced_size (n : Nat) : (balanced n).size = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simp [balanced, Tree.size]
    | succ n =>
      rw [balanced, Tree.size, ih ((n + 1) / 2) (by omega), ih (n / 2) (by omega)]
      omega

/-- Fewer than `2^(h+1)` keys put every key at depth at most `h`. -/
theorem balanced_depth_of_lt_pow (h : Nat) :
    ∀ n x, n < 2 ^ (h + 1) → x < n → (balanced n).depth x ≤ h := by
  induction h with
  | zero =>
    intro n x hn hx
    have hn1 : n = 1 := by simp at hn; omega
    subst hn1
    have hx0 : x = 0 := by omega
    subst hx0
    simp [balanced, Tree.depth, Tree.size]
  | succ h ih =>
    intro n x hn hx
    cases n with
    | zero => omega
    | succ n =>
      have power : 2 ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 := Nat.pow_succ ..
      rw [power] at hn
      rw [balanced, Tree.depth, balanced_size]
      split_ifs with hl he
      · have := ih ((n + 1) / 2) x (by omega) hl
        omega
      · omega
      · have := ih (n / 2) (x - (n + 1) / 2 - 1) (by omega) (by omega)
        omega

theorem balanced_depth (n x : Nat) (hx : x < n) : (balanced n).depth x ≤ Nat.log2 n :=
  balanced_depth_of_lt_pow (Nat.log2 n) n x Nat.lt_log2_self hx

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

theorem log2_le_logb (n : Nat) (hn : n ≠ 0) : (Nat.log2 n : ℝ) ≤ Real.logb 2 n := by
  have hp : ((2 ^ Nat.log2 n : Nat) : ℝ) ≤ n := by exact_mod_cast Nat.log2_self_le hn
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hp
  simpa [Real.logb_pow] using this

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
  · have hl := log2_le_logb n hn
    have hm := mul_le_mul_of_nonneg_left (show (Nat.log2 n : ℝ) + 1 ≤ 1 + Real.logb 2 n by linarith)
      (Nat.cast_nonneg (α := ℝ) xs.length)
    linarith

end RotationBST.Classical.Static
