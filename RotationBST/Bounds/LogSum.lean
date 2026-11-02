module

public import RotationBST.Splay.Logarithms
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace RotationBST.Bounds

/-- Finite Jensen inequality for positive integer gaps, with an upper bound on
 their sum. The empty list is included using Lean's total division convention. -/
theorem logSum_le (gs : List Nat) (positive : ∀ g ∈ gs, 0 < g)
    (M : ℝ) (hM : (gs.sum : ℝ) ≤ M) :
    (gs.map fun g : Nat => Real.logb 2 g).sum ≤
      (gs.length : ℝ) * Real.logb 2 (M / gs.length) := by
  by_cases he : gs = []
  · subst gs; simp
  · have hq : (0 : ℝ) < gs.length := by exact_mod_cast List.length_pos_iff.mpr he
    have hs : 0 < gs.sum := by
      cases gs with
      | nil => contradiction
      | cons g gs =>
          have := positive g (by simp)
          simp only [List.sum_cons]; omega
    have hMpos : 0 < M := lt_of_lt_of_le (by exact_mod_cast hs) hM
    let avg := M / gs.length
    have havg : 0 < avg := div_pos hMpos hq
    have each (g : Nat) (hg : g ∈ gs) :
        Real.log g ≤ Real.log avg + (g : ℝ) / avg - 1 := by
      have hgpos : (0 : ℝ) < g := by exact_mod_cast positive g hg
      have h := Real.log_le_sub_one_of_pos (div_pos hgpos havg)
      rw [Real.log_div hgpos.ne' havg.ne'] at h
      linarith
    have sumBound : (gs.map fun g : Nat => Real.log g).sum ≤
        (gs.length : ℝ) * Real.log avg + (gs.sum : ℝ) / avg - gs.length := by
      have aux (ls : List Nat) (hh : ∀ g ∈ ls,
          Real.log g ≤ Real.log avg + (g : ℝ) / avg - 1) :
          (ls.map fun g : Nat => Real.log g).sum ≤
            (ls.length : ℝ) * Real.log avg + (ls.sum : ℝ) / avg - ls.length := by
        induction ls with
        | nil => simp
        | cons g ls ih =>
            have h₁ := hh g (by simp)
            have h₂ := ih (by intro g hg; exact hh g (by simp [hg]))
            simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
              Nat.cast_one, add_div]
            nlinarith
      exact aux gs each
    have hdiv := div_le_div_of_nonneg_right hM havg.le
    have heq : M / avg = gs.length := by
      dsimp [avg]
      field_simp
    rw [heq] at hdiv
    have hnatlog : (gs.map fun g : Nat => Real.log g).sum ≤
        (gs.length : ℝ) * Real.log avg := by linarith
    have hbin := div_le_div_of_nonneg_right hnatlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hsum : (gs.map fun g : Nat => Real.logb 2 g).sum =
        (gs.map fun g : Nat => Real.log g).sum / Real.log 2 := by
      have aux (ls : List Nat) : (ls.map fun g : Nat => Real.logb 2 g).sum =
          (ls.map fun g : Nat => Real.log g).sum / Real.log 2 := by
        induction ls with
        | nil => simp
        | cons g ls ih =>
            simp only [List.map_cons, List.sum_cons]
            rw [ih, Real.logb, add_div]
      exact aux gs
    rw [hsum]
    simpa only [Real.logb, mul_div_assoc] using hbin

end RotationBST.Bounds
