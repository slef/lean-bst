module

public import RotationBST.Algorithms.Splay.StaticOptimality
public import RotationBST.Algorithms.Splay.Snapshot.Definitions.Abstract

@[expose] public section

namespace RotationBST.Splay

theorem snapshotSum_succ (n : Nat) (p : Nat → ℝ) (t : Tree) (m : Nat) :
    (∑ j ∈ Finset.range (m + 1), snapshotAt n p t j) = meanSearch n p t +
      ∑ x ∈ Finset.range n, p x * ∑ j ∈ Finset.range m, snapshotAt n p (run t x).1 j := by
  rw [Finset.sum_range_succ']
  simp only [snapshotAt]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  ring

/-- A weighted access lemma averaged over one independent request. -/
theorem mean_access (n : Nat) (p w : Nat → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hnorm : ∑ i ∈ Finset.range n, p i = 1) (hw : ∀ i, 0 < w i)
    (t : Tree) (hn : t.size = n) (W : ℝ) (hmass : mass w t 0 = W) :
    meanSearch n p t + (∑ x ∈ Finset.range n, p x * potential w (run t x).1 0) ≤
      2 + 3 * (∑ x ∈ Finset.range n, p x * (Real.logb 2 W - Real.logb 2 (w x))) +
        potential w t 0 := by
  have hpoint (x : Nat) (hx : x ∈ Finset.range n) :
      p x * (run t x).2 + p x * potential w (run t x).1 0 ≤
        p x + 3 * (p x * (Real.logb 2 W - Real.logb 2 (w x))) + p x * potential w t 0 := by
    have h := mul_le_mul_of_nonneg_left
      (access_lemma w hw t x (by rw [hn]; exact Finset.mem_range.mp hx)) (hp x)
    rw [hmass] at h
    nlinarith
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hnorm, one_mul] at hsum
  unfold meanSearch
  linarith

theorem snapshotSum_weighted (n : Nat) (p w : Nat → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hnorm : ∑ i ∈ Finset.range n, p i = 1) (hw : ∀ i, 0 < w i)
    (lower W : ℝ) (hlower : 0 < lower) (hwlower : ∀ i, lower ≤ w i)
    (m : Nat) (t : Tree) (hn : t.size = n) (hmass : mass w t 0 = W) :
    (∑ j ∈ Finset.range m, snapshotAt n p t j) ≤
      (m : ℝ) * (2 + 3 * ∑ x ∈ Finset.range n, p x * (Real.logb 2 W - Real.logb 2 (w x))) +
        potential w t 0 - (n : ℝ) * Real.logb 2 lower := by
  induction m generalizing t with
  | zero =>
      have h := (potential_bounds w hw lower W hlower hwlower t 0 hmass.le).1
      rw [hn] at h
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, zero_add]
      linarith
  | succ m ih =>
      have hpoint (x : Nat) (hx : x ∈ Finset.range n) :=
        (run_correct t x (by rw [hn]; exact Finset.mem_range.mp hx)).1.1
      have hnext (x : Nat) (hx : x ∈ Finset.range n) :=
        mul_le_mul_of_nonneg_left (ih (run t x).1
          ((hpoint x hx).size_eq.symm.trans hn)
          ((mass_rotations w (hpoint x hx) 0).symm.trans hmass)) (hp x)
      have hsum := Finset.sum_le_sum hnext
      simp_rw [mul_sub, mul_add] at hsum
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, hnorm, one_mul] at hsum
      have hb := mean_access n p w hp hnorm hw t hn W hmass
      rw [snapshotSum_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      simp_rw [mul_sub] at hb ⊢
      simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hnorm, one_mul] at hb ⊢
      nlinarith

/-- Finite-expectation version of telescoping the weighted access lemma. -/
theorem snapshot_weighted (n : Nat) (p w : Nat → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hnorm : ∑ i ∈ Finset.range n, p i = 1) (hw : ∀ i, 0 < w i)
    (lower W : ℝ) (hlower : 0 < lower) (hwlower : ∀ i, lower ≤ w i)
    (m : Nat) (hm : 0 < m) (t : Tree) (hn : t.size = n) (hmass : mass w t 0 = W) :
    snapshotMean n p t m ≤
      2 + 3 * (∑ x ∈ Finset.range n, p x * (Real.logb 2 W - Real.logb 2 (w x))) +
        (n : ℝ) * (Real.logb 2 W - Real.logb 2 lower) / m := by
  have hb := snapshotSum_weighted n p w hp hnorm hw lower W hlower hwlower m t hn hmass
  have hi := potential_upper w hw t 0 W hmass.le
  rw [hn] at hi
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold snapshotMean
  apply (div_le_iff₀ hm').mpr
  rw [add_mul, div_mul_cancel₀ _ hm'.ne']
  nlinarith

/-- Snapshot theorem: run independent searches, and stop uniformly before one
of the first `m` searches. Its expected static search cost is close to entropy.
The smoothing of zero probabilities is internal to the proof. -/
theorem snapshot_bound (t : Tree) (p : Nat → ℝ) (nonnegative : ∀ i, 0 ≤ p i)
    (normalized : ∑ i ∈ Finset.range t.size, p i = 1) (m : Nat) (hm : 0 < m) :
    snapshotMean t.size p t m ≤ 5 + 3 * probabilityEntropy t.size p +
      (t.size : ℝ) * (1 + Real.logb 2 t.size) / m := by
  have hn : 0 < t.size := by
    by_contra h
    have hz : t.size = 0 := by omega
    simp [hz] at normalized
  have hn' : (0 : ℝ) < t.size := by exact_mod_cast hn
  let w : Nat → ℝ := fun i => p i + 1 / (t.size : ℝ)
  have hw : ∀ i, 0 < w i := by intro i; exact add_pos_of_nonneg_of_pos (nonnegative i) (by positivity)
  have hlow : ∀ i, 1 / (t.size : ℝ) ≤ w i := by
    intro i; dsimp only [w]; linarith [nonnegative i]
  have hmass : mass w t 0 = 2 := by
    rw [mass_eq_finset]
    change (∑ i ∈ Finset.range t.size, (p i + 1 / (t.size : ℝ))) = 2
    rw [Finset.sum_add_distrib, normalized]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  have hb := snapshot_weighted t.size p w nonnegative normalized hw (1 / (t.size : ℝ)) 2
    (by positivity) hlow m hm t rfl hmass
  have hpoint (x : Nat) : p x * (Real.logb 2 2 - Real.logb 2 (w x)) ≤
      p x + p x * Real.logb 2 (1 / p x) := by
    by_cases hx : p x = 0
    · simp [hx]
    · have hp : 0 < p x := lt_of_le_of_ne (nonnegative x) (Ne.symm hx)
      have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp
        (show p x ≤ w x from le_add_of_nonneg_right (by positivity))
      have hh := mul_le_mul_of_nonneg_left hl (nonnegative x)
      rw [Real.logb_self_eq_one (by norm_num), Real.logb_div one_ne_zero hx, Real.logb_one]
      linarith
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.range t.size) => hpoint x)
  rw [Finset.sum_add_distrib, normalized] at hsum
  change _ ≤ 1 + probabilityEntropy t.size p at hsum
  rw [Real.logb_self_eq_one (by norm_num)] at hsum
  rw [Real.logb_self_eq_one (by norm_num), Real.logb_div one_ne_zero hn'.ne', Real.logb_one] at hb
  simp only [zero_sub, sub_neg_eq_add] at hb
  linarith

end RotationBST.Splay
