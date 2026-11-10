module

public import RotationBST.Bounds.Implications.Properties
public import RotationBST.Bounds.Implications.StaticFinger
public import RotationBST.Bounds.DynamicFinger.Proofs
public import RotationBST.Bounds.Implications.Logarithmic

@[expose] public section

namespace RotationBST

/-- Working set implies static optimality for every algorithm, independently of
its implementation. Total cost includes requests as well as rotations. -/
theorem HasWorkingSetBound.staticOptimality (a : Algorithm) (h : HasWorkingSetBound a) :
    HasStaticOptimalityBound a := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨C + 1, C + D, ?_⟩
  intro t xs valid
  have hc : (a.cost t xs : ℝ) ≤ (C : ℝ) * workingSetSum t.size [] xs +
      (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ)) := by exact_mod_cast h t xs valid
  have hs := Bounds.workingSet_le_static t.size xs valid
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) C)
  have hl := Bounds.length_le_staticCost t.size xs
  simp only [Algorithm.totalCost, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- Static optimality implies the static-finger bound by reciprocal-square
weights around the fixed finger. -/
theorem HasStaticOptimalityBound.staticFinger (a : Algorithm) (h : HasStaticOptimalityBound a) :
    HasStaticFingerBound a := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨3 * C, D, ?_⟩
  intro t xs f _ valid
  have hc := h t xs valid
  have hs := Bounds.static_le_finger t.size f xs valid
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) C)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- Working set implies the static-finger bound, for any online rule. -/
theorem HasWorkingSetBound.staticFinger (a : Algorithm) (h : HasWorkingSetBound a) :
    HasStaticFingerBound a :=
  (h.staticOptimality a).staticFinger a

/-- Dynamic finger implies static finger: start the dynamic-finger sum at the
fixed finger, where it is at most twice the static-finger sum. -/
theorem HasDynamicFingerBound.staticFinger (a : Algorithm) (h : HasDynamicFingerBound a) :
    HasStaticFingerBound a := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨2 * C, D, ?_⟩
  intro t xs f hf valid
  have hc := h t xs f hf valid
  have hs := Bounds.dynamicFingerCostFrom_finger_le f xs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℝ) C)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

end RotationBST
