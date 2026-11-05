module

public import RotationBST.Bounds.LazyFinger.Random.Exterior
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger.RandomAnalysis

noncomputable def pairTerm (w : Nat → ℝ) (x y a : Nat) : ℝ :=
  w a / segment w (min a x) (max a x + 1) +
  w a / segment w (min a y) (max a y + 1) -
  2 * (w a / segment w (min a (min x y)) (max a (max x y) + 1))

theorem pairTerm_left (w : Nat → ℝ) (x y a : Nat) (hxy : x ≤ y) (ha : a < x) :
    pairTerm w x y a = w a / segment w a (x + 1) - w a / segment w a (y + 1) := by
  have hax : a ≤ x := by omega
  have hay : a ≤ y := by omega
  simp only [pairTerm, min_eq_left hxy, max_eq_right hxy,
    min_eq_left hax, max_eq_right hax, min_eq_left hay, max_eq_right hay]
  ring

theorem pairTerm_middle (w : Nat → ℝ) (x y a : Nat) (hxa : x ≤ a) (hay : a ≤ y) :
    pairTerm w x y a = w a / segment w x (a + 1) + w a / segment w a (y + 1) -
      2 * (w a / segment w x (y + 1)) := by
  have hxy : x ≤ y := by omega
  simp only [pairTerm, min_eq_left hxy, max_eq_right hxy,
    min_eq_right hxa, max_eq_left hxa, min_eq_left hay, max_eq_right hay]

theorem pairTerm_right (w : Nat → ℝ) (x y a : Nat) (hxy : x ≤ y) (ha : y < a) :
    pairTerm w x y a = w a / segment w y (a + 1) - w a / segment w x (a + 1) := by
  have hxa : x ≤ a := by omega
  have hya : y ≤ a := by omega
  simp only [pairTerm, min_eq_left hxy, max_eq_right hxy,
    min_eq_right hxa, max_eq_left hxa, min_eq_right hya, max_eq_left hya]
  ring

theorem middle_bound (w : Nat → ℝ) (x y : Nat) (hxy : x ≤ y)
    (hw : ∀ k ∈ Finset.Ico x (y + 1), 0 < w k) :
    ∑ a ∈ Finset.Ico x (y + 1), pairTerm w x y a ≤
      (Real.log (segment w x (y + 1)) - Real.log (w x)) +
      (Real.log (segment w x (y + 1)) - Real.log (w y)) := by
  have he : (∑ a ∈ Finset.Ico x (y + 1), pairTerm w x y a) =
      (∑ a ∈ Finset.Ico x (y + 1), w a / segment w x (a + 1)) +
      (∑ a ∈ Finset.Ico x (y + 1), w a / segment w a (y + 1)) - 2 := by
    rw [Finset.sum_congr rfl (fun a ha => pairTerm_middle w x y a
      (Finset.mem_Ico.mp ha).1 (by have := (Finset.mem_Ico.mp ha).2; omega))]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    have hp := segment_pos w x (y + 1) (by omega) hw
    change _ + _ - 2 * (segment w x (y + 1) / segment w x (y + 1)) = _
    rw [div_self hp.ne', mul_one]
  rw [he]
  linarith [interior_forward w x y hxy hw, interior_backward w x y hxy hw]

/-- Three interval pieces telescope to a bound involving only endpoint weights
and the mass between the endpoints. -/
theorem sum_pairTerm_le (w : Nat → ℝ) (lo hi x y : Nat)
    (hlo : lo ≤ x) (hxy : x ≤ y) (hhi : y < hi)
    (hw : ∀ k ∈ Finset.Ico lo hi, 0 < w k) :
    ∑ a ∈ Finset.Ico lo hi, pairTerm w x y a ≤
      2 * (Real.log (segment w x (y + 1)) - Real.log (w x)) +
      2 * (Real.log (segment w x (y + 1)) - Real.log (w y)) := by
  have hleft := exterior_left w lo x y hlo hxy (by
    intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
  have hright := exterior_right w x y hi hxy hhi (by
    intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
  have hmid := middle_bound w x y hxy (by
    intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
  have el : (∑ a ∈ Finset.Ico lo x, pairTerm w x y a) =
      ∑ a ∈ Finset.Ico lo x, (w a / segment w a (x + 1) - w a / segment w a (y + 1)) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact pairTerm_left w x y a hxy (Finset.mem_Ico.mp ha).2
  have er : (∑ a ∈ Finset.Ico (y + 1) hi, pairTerm w x y a) =
      ∑ a ∈ Finset.Ico (y + 1) hi, (w a / segment w y (a + 1) - w a / segment w x (a + 1)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply pairTerm_right w x y a hxy
    have := (Finset.mem_Ico.mp ha).1
    omega
  have hsplit := Finset.sum_Ico_consecutive (pairTerm w x y) hlo (show x ≤ hi by omega)
  have hsplit' := Finset.sum_Ico_consecutive (pairTerm w x y) (show x ≤ y + 1 by omega)
    (show y + 1 ≤ hi by omega)
  rw [el] at hsplit
  rw [er] at hsplit'
  linarith

end RotationBST.LazyFinger.RandomAnalysis
