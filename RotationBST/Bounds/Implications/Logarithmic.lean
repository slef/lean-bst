module

public import RotationBST.Bounds.Abstract
public import RotationBST.Bounds.Logarithmic.Abstract

@[expose] public section

/-! The static-finger sum is at most the logarithmic baseline, because every
distance between two of `n` keys is less than `n`. -/
namespace RotationBST

theorem Bounds.fingerCost_le_logCost (n f : Nat) (xs : List Nat)
    (hf : f < n) (valid : ∀ x ∈ xs, x < n) :
    Bounds.fingerCost f xs ≤ Bounds.logCost n xs := by
  induction xs with
  | nil => simp [Bounds.fingerCost, Bounds.logCost]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have hrest := ih (fun y hy => valid y (by simp [hy]))
    have hd : Nat.dist x f + 1 ≤ n := by
      unfold Nat.dist; omega
    have hlog : Real.logb 2 (Nat.dist x f + 1 : Nat) ≤ Real.logb 2 n :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by exact_mod_cast hd)
    simp only [Bounds.fingerCost, Bounds.logCost, List.map_cons, List.sum_cons,
      List.length_cons, Nat.cast_add, Nat.cast_one] at hrest hlog ⊢
    nlinarith

private theorem Algorithm.cost_nil (a : Algorithm) (t : Tree) : a.cost t [] = 0 := rfl

/-- Static finger implies the logarithmic bound, with the same constants: put
the finger at rank zero. An empty tree admits only the empty sequence. -/
theorem HasStaticFingerBound.logarithmic (a : Algorithm) (h : HasStaticFingerBound a) :
    HasLogarithmicBound a := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨C, D, ?_⟩
  intro t xs valid
  by_cases hn : t.size = 0
  · have hxs : xs = [] := by
      cases xs with
      | nil => rfl
      | cons x xs => have := valid x (by simp); omega
    subst hxs
    simp [Algorithm.totalCost, Algorithm.cost_nil, Bounds.logCost, hn]
  · have hc := h t xs 0 (by omega) valid
    have hs := Bounds.fingerCost_le_logCost t.size 0 xs (by omega) valid
    have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) C)
    linarith

end RotationBST
