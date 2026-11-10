module

public import RotationBST.Bounds.Abstract
public import RotationBST.Bounds.DynamicFinger.Definitions.Abstract

@[expose] public section

/-! Dynamic finger against a fixed finger: the triangle inequality through the
finger splits each step's logarithm into the logarithms of its two endpoints. -/
namespace RotationBST.Bounds

/-- Distances through a fixed point multiply: `d(a,b) + 1 ≤ (d(a,f) + 1)(d(b,f) + 1)`. -/
theorem dist_succ_le_mul (a b f : Nat) :
    Nat.dist a b + 1 ≤ (Nat.dist a f + 1) * (Nat.dist b f + 1) := by
  have h := Nat.dist.triangle_inequality a f b
  rw [Nat.dist_comm f b] at h
  nlinarith [Nat.zero_le (Nat.dist a f * Nat.dist b f)]

/-- One dynamic-finger step costs at most the finger costs of its two endpoints. -/
theorem logb_dist_le_finger (a b f : Nat) :
    Real.logb 2 (Nat.dist a b + 1 : Nat) ≤
      Real.logb 2 (Nat.dist a f + 1 : Nat) + Real.logb 2 (Nat.dist b f + 1 : Nat) := by
  rw [← Real.logb_mul (by positivity) (by positivity)]
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  exact_mod_cast dist_succ_le_mul a b f

theorem logb_dist_finger_nonneg (p f : Nat) : 0 ≤ Real.logb 2 (Nat.dist p f + 1 : Nat) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))

/-- Each request is charged at most twice, once as a target and once as the
source of the next step; the first source is the start key `p`. -/
theorem dynamicFingerCostFrom_le_fingerCost (f p : Nat) (xs : List Nat) :
    dynamicFingerCostFrom p xs ≤
      2 * fingerCost f xs + Real.logb 2 (Nat.dist p f + 1 : Nat) := by
  induction xs generalizing p with
  | nil => simpa [dynamicFingerCostFrom, fingerCost] using logb_dist_finger_nonneg p f
  | cons x xs ih =>
      have hstep := logb_dist_le_finger p x f
      have hx := logb_dist_finger_nonneg x f
      have hrest := ih x
      simp only [fingerCost, List.map_cons, List.sum_cons] at hrest ⊢
      simp only [dynamicFingerCostFrom]
      linarith

/-- With the start key at the finger, the start term vanishes. -/
theorem dynamicFingerCostFrom_finger_le (f : Nat) (xs : List Nat) :
    dynamicFingerCostFrom f xs ≤ 2 * fingerCost f xs := by
  simpa using dynamicFingerCostFrom_le_fingerCost f f xs

end RotationBST.Bounds
