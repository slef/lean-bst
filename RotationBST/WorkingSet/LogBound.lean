module

public import RotationBST.Splay.AccessLemma
public import RotationBST.WorkingSet.Reweight
public import RotationBST.WorkingSet.Abstract

@[expose] public section

namespace RotationBST.Recency

theorem logb_nat_le (n : Nat) : Real.logb 2 n ≤ (n.log2 : ℝ) + 1 := by
  have h := Nat.lt_floor_add_one (Real.logb 2 n)
  rw [show ⌊Real.logb 2 (n : ℝ)⌋₊ = n.log2 by
    simpa only [Nat.cast_ofNat] using (Real.natFloor_logb_natCast 2 n).trans Nat.log2_eq_log_two.symm] at h
  exact h.le

/-- The amortized cost of one splay is controlled by its pre-access recency rank. -/
theorem access_bound (order : List Nat) (t : Tree) (x : Nat)
    (hp : order.Perm (List.range t.size)) (hx : x < t.size) :
    ((Splay.run t x).2 : ℝ) +
      Splay.potential (weight (touch order x)) (Splay.run t x).1 0 -
      Splay.potential (weight order) t 0 ≤
        10 * (1 + ((order.idxOf x + 1).log2 : ℝ)) := by
  have ha := (Splay.run_correct t x hx).1
  have hb := Splay.access_lemma (weight order) (weight_pos order) t x hx
  have ht : 0 < Splay.mass (weight order) t 0 := by
    cases t with
    | nil => simp [Tree.size] at hx
    | node l r => exact Splay.mass_pos _ (weight_pos order) l r 0
  have hm : Splay.mass (weight order) t 0 ≤ 2 := by
    rw [mass_weight order t hp]
    exact squareSum_le_two _
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ht hm
  rw [Real.logb_self_eq_one (by norm_num)] at hlog
  have hrank := logb_nat_le (order.idxOf x + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hrank
  simp only [weight, Real.logb_inv, Real.logb_pow, Nat.cast_ofNat] at hb
  have hpot : Splay.potential (weight (touch order x)) (Splay.run t x).1 0 ≤
      Splay.potential (weight order) (Splay.run t x).1 0 := by
    generalize he : (Splay.run t x).1 = u at ha ⊢
    cases u with
    | nil => exact ha.2.elim
    | node l r =>
        have hroot : l.size = x := ha.2
        rw [← hroot]
        apply touch_potential order l r
        rw [← ha.1.size_eq]
        exact hp
  have hn : 0 ≤ ((order.idxOf x + 1).log2 : ℝ) := Nat.cast_nonneg _
  linarith

end RotationBST.Recency
