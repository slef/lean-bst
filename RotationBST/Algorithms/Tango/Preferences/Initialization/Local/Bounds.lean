module

public import RotationBST.Algorithms.Tango.Preferences.Initialization.Local.Definitions.Abstract
public import RotationBST.Algorithms.Tango.Preferences.Initialization.Accounting
public import RotationBST.Algorithms.Tango.Reference.Bounds
public import RotationBST.Bounds.Implications.Entropy
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tango.Initialization

/-- Even a partially filled tree has no more total subtree height than the
complete binary tree at the same height. -/
theorem heightSum_cap (t : Tree) (h : Nat) (cap : height t ≤ h) :
    heightSum t + h + 2 ≤ 2 ^ (h + 1) := by
  induction h generalizing t with
  | zero =>
    cases t with
    | nil => simp [heightSum]
    | node l r => simp [height] at cap
  | succ h ih =>
    cases t with
    | nil =>
      have previous := ih .nil (by simp [height])
      simp only [heightSum] at previous ⊢
      rw [Nat.pow_succ]
      omega
    | node l r =>
      have left := ih l (by simp only [height] at cap; omega)
      have right := ih r (by simp only [height] at cap; omega)
      simp only [heightSum]
      rw [Nat.pow_succ]
      omega

/-- The balanced reference has linear total subtree height for every size,
including incomplete final levels and the empty tree. -/
theorem balanced_heightSum (n : Nat) : heightSum (balanced n) ≤ 4 * n := by
  by_cases empty : n = 0
  · subst n; simp [balanced, heightSum]
  have cap := heightSum_cap (balanced n) (Nat.log2 n + 1) (balanced_height n)
  have power : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  have square : 2 ^ (Nat.log2 n + 1 + 1) = 4 * 2 ^ Nat.log2 n := by
    simp only [Nat.pow_succ]
    omega
  rw [square] at cap
  omega

private theorem log_le_height (h : Nat) : Real.logb 2 h ≤ (h : ℝ) + 1 := by
  have small : Nat.log2 h ≤ h := Nat.log2_le_self h
  have logarithm := Bounds.logb_nat_le h
  exact logarithm.trans (by exact_mod_cast Nat.add_le_add_right small 1)

theorem localAllowance_height (t : Tree) :
    localAllowance t ≤ 8 * (heightSum t : ℝ) + 10 * t.size := by
  induction t with
  | nil => simp [localAllowance, heightSum, Tree.size]
  | node l r il ir =>
    have logarithm := log_le_height (height (.node l r))
    simp only [localAllowance, heightSum, Tree.size, Nat.cast_add, Nat.cast_one]
    linarith

/-- The full local logarithmic allowance is linear, rather than n log log n. -/
theorem balanced_localAllowance (n : Nat) : localAllowance (balanced n) ≤ 42 * n := by
  have bound := localAllowance_height (balanced n)
  rw [balanced_size] at bound
  have heights : (heightSum (balanced n) : ℝ) ≤ 4 * n := by exact_mod_cast balanced_heightSum n
  linarith

private theorem allowance_congr (t : Tree) (lo : Nat) (v w : Nat → ℝ)
    (same : ∀ key, lo ≤ key → key < lo + t.size → v key = w key) :
    allowance t lo v = allowance t lo w := by
  rw [allowance_eq_sum, allowance_eq_sum]
  congr 1
  apply List.map_congr_left
  intro key member
  obtain ⟨i, upper, eq⟩ := List.mem_range'.mp member
  exact same key (by omega) (by omega)

/-- Indexed credit agrees with its structural sum; offsets introduce no loss. -/
theorem allowance_localCredit (t : Tree) (lo : Nat) :
    allowance t lo (fun key => localCredit t (key - lo)) = localAllowance t := by
  induction t generalizing lo with
  | nil => rfl
  | node l r il ir =>
    have left : allowance l lo (fun key => localCredit (.node l r) (key - lo)) = localAllowance l := by
      rw [← il lo]
      apply allowance_congr
      intro key lower upper
      simp only [localCredit, heightAt, ite_eq_left (show key - lo < l.size by omega)]
    have right : allowance r (lo + l.size + 1) (fun key => localCredit (.node l r) (key - lo)) = localAllowance r := by
      rw [← ir (lo + l.size + 1)]
      apply allowance_congr
      intro key lower upper
      have less : ¬ key - lo < l.size := by omega
      have eq : ¬ key - lo = l.size := by omega
      have sub : key - lo - l.size - 1 = key - (lo + l.size + 1) := by omega
      simp only [localCredit, heightAt, ite_eq_right less, ite_eq_right eq, sub]
    simp only [allowance, left, right, localAllowance]
    simp [localCredit, heightAt]

theorem localCredit_nonneg (t : Tree) (key : Nat) : 0 ≤ localCredit t key := by
  unfold localCredit
  have bound := Bounds.logb_nat_nonneg (heightAt t key)
  linarith

/-- The generated first-setting events spend at most linear local credit,
independently of sequence length or which keys are eventually requested. -/
theorem balanced_firstCharge (n : Nat) (xs : List Nat) (valid : ∀ key ∈ xs, key < n) :
    firstCharge (preferenceLog (balanced n) [] xs) (localCredit (balanced n)) ≤ 42 * n := by
  have bound := first_budget (balanced n) xs (localCredit (balanced n))
    (by simpa only [balanced_size] using valid) (fun key _ => localCredit_nonneg _ key)
  have total := allowance_localCredit (balanced n) 0
  simp only [Nat.sub_zero] at total
  rw [total] at bound
  exact bound.trans (balanced_localAllowance n)

/-- Resumed histories can use only the local credit not already spent. -/
theorem balanced_remainingCharge (n : Nat) (past xs : List Nat)
    (valid : ∀ key ∈ xs, key < n) :
    firstCharge (preferenceLog (balanced n) past xs) (localCredit (balanced n)) ≤
      42 * n - observedCharge (balanced n) 0 past (localCredit (balanced n)) := by
  have bound := remaining_budget (balanced n) past xs (localCredit (balanced n))
    (by simpa only [balanced_size] using valid) (fun key _ => localCredit_nonneg _ key)
  have total := allowance_localCredit (balanced n) 0
  simp only [Nat.sub_zero] at total
  rw [total] at bound
  linarith [balanced_localAllowance n]

end RotationBST.Tango.Initialization
