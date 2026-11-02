module

public import RotationBST.Bounds.Unified.Abstract
public import RotationBST.Splay.MixedWeights
public import RotationBST.Splay.StaticOptimality
public import RotationBST.Bounds.StaticFinger

@[expose] public section

/-! The unified bound here is Sleator--Tarjan's fixed-finger theorem (1985,
Theorem 5), not the later dynamic unified bound conjecture. -/
namespace RotationBST.Splay
open Recency

noncomputable def unifiedFixed (original : List Nat) (f x : Nat) : ℝ :=
  (original.count x : ℝ) / original.length + Bounds.fingerWeight f x

theorem unifiedFixed_nonneg (original : List Nat) (f : Nat) : ∀ i, 0 ≤ unifiedFixed original f i := by
  intro i
  exact add_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Bounds.fingerWeight_pos f i).le

theorem unifiedFixed_mass (original : List Nat) (f : Nat) (t : Tree)
    (valid : ∀ x ∈ original, x < t.size) : mass (unifiedFixed original f) t 0 ≤ 5 := by
  rw [mass_eq_finset]
  simp only [unifiedFixed, Finset.sum_add_distrib, ← Finset.sum_div]
  rw [Bounds.sum_count t.size original valid]
  have hf := Bounds.fingerWeight_sum t.size f
  by_cases hm : original.length = 0
  · simp only [hm, Nat.cast_zero, zero_div]; linarith
  · rw [div_self (by exact_mod_cast hm : (original.length : ℝ) ≠ 0)]
    linarith

/-- Every one-step charge takes the best of the three bounds, not a single
choice made for the whole sequence. -/
theorem unified_access (original past : List Nat) (f : Nat) (t : Tree) (x : Nat)
    (originalValid : ∀ y ∈ original, y < t.size)
    (pastValid : ∀ y ∈ past, y < t.size) (hx : x ∈ original) :
    ((run t x).2 : ℝ) +
      potential (mixedWeight (unifiedFixed original f) (recent t.size (past ++ [x]))) (run t x).1 0 -
      potential (mixedWeight (unifiedFixed original f) (recent t.size past)) t 0 ≤
      10 * unifiedCharge t.size f original past x := by
  let order := recent t.size past
  let fixed := unifiedFixed original f
  let w := mixedWeight fixed order
  have hpos := mixedWeight_pos fixed (unifiedFixed_nonneg original f) order
  have hvalid := originalValid x hx
  have hp := recent_perm t.size past pastValid
  have hb := mixed_access fixed (unifiedFixed_nonneg original f) order t x hp hvalid
  have hmass : mass w t 0 ≤ 7 := by
    change mass (fun i => weight order i + fixed i) t 0 ≤ 7
    rw [mass_add, mass_weight order t hp]
    have := squareSum_le_two t.size
    have := unifiedFixed_mass original f t originalValid
    dsimp only [fixed]
    linarith
  have hmpos : 0 < mass w t 0 := by
    cases t with
    | nil => simp [Tree.size] at hvalid
    | node l r => exact mass_pos w hpos l r 0
  have hlog : Real.logb 2 (mass w t 0) ≤ 3 := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hmpos
      (show mass w t 0 ≤ (2 : ℝ) ^ 3 by norm_num; linarith)
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hh
    norm_num at hh
    exact hh
  have hrec : weight order x ≤ w x := le_add_of_nonneg_right (unifiedFixed_nonneg original f x)
  have hlrec := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (weight_pos order x) hrec
  simp only [weight, Real.logb_inv, Real.logb_pow, Nat.cast_ofNat] at hlrec
  have hrank := rank_le_workingSet t.size x past pastValid hvalid
  have hrlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < ((order.idxOf x + 1 : Nat) : ℝ))
    (show ((order.idxOf x + 1 : Nat) : ℝ) ≤ workingSetNumber t.size past x by exact_mod_cast hrank)
  simp only [Nat.cast_add, Nat.cast_one] at hrlog
  have hq : (0 : ℝ) < original.count x := by exact_mod_cast List.count_pos_iff.mpr hx
  have hqm : (original.count x : ℝ) ≤ original.length := by exact_mod_cast List.count_le_length
  have hm : (0 : ℝ) < original.length := lt_of_lt_of_le hq hqm
  have hfreq : (original.count x : ℝ) / original.length ≤ w x := by
    dsimp only [w, mixedWeight, fixed, unifiedFixed]
    linarith [weight_pos order x, Bounds.fingerWeight_pos f x]
  have hlfreq := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (div_pos hq hm) hfreq
  have hfinger : Bounds.fingerWeight f x ≤ w x := by
    dsimp only [w, mixedWeight, fixed, unifiedFixed]
    linarith [weight_pos order x, div_pos hq hm]
  have hlfinger := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Bounds.fingerWeight_pos f x) hfinger
  simp only [Bounds.fingerWeight, Real.logb_inv, Real.logb_pow, Nat.cast_ofNat] at hlfinger
  have hfreqlog : 0 ≤ Real.logb 2 ((original.length : ℝ) / original.count x) :=
    Real.logb_nonneg (by norm_num) ((le_div_iff₀ hq).mpr (by simpa using hqm))
  have hwslog : 0 ≤ Real.logb 2 (workingSetNumber t.size past x) := Bounds.logb_nat_nonneg _
  have hdlog : 0 ≤ Real.logb 2 (Nat.dist x f + 1 : Nat) := Bounds.logb_nat_nonneg _
  rw [Real.logb_div hq.ne' hm.ne'] at hlfreq
  rw [Real.logb_div hm.ne' hq.ne'] at hfreqlog
  rw [recent_step]
  change ((run t x).2 : ℝ) + potential (mixedWeight fixed (touch order x)) (run t x).1 0 -
    potential w t 0 ≤ 10 * unifiedCharge t.size f original past x
  unfold unifiedCharge
  simp only [Real.logb_div hm.ne' hq.ne', Nat.cast_add, Nat.cast_one]
  simp only [Nat.cast_add, Nat.cast_one] at hdlog
  dsimp only [w] at hlog hlrec hlfreq hlfinger ⊢
  rcases le_total (Real.logb 2 ((original.length : ℝ) / original.count x))
      (Real.logb 2 (Nat.dist x f + 1 : Nat)) with h | h
  all_goals simp only [Real.logb_div hm.ne' hq.ne', Nat.cast_add, Nat.cast_one] at h
  · rw [min_eq_left h]
    rcases le_total (Real.logb 2 (workingSetNumber t.size past x))
      (Real.logb 2 (original.length : ℝ) - Real.logb 2 (original.count x : ℝ)) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith
  · rw [min_eq_right h]
    rcases le_total (Real.logb 2 (workingSetNumber t.size past x))
      (Real.logb 2 ((Nat.dist x f : ℝ) + 1)) with h' | h'
    · rw [min_eq_left h']; linarith
    · rw [min_eq_right h']; linarith

end RotationBST.Splay
