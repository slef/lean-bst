module

public import RotationBST.Bounds.LazyFinger.Random.LogSteps
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger.RandomAnalysis

/-- Half-open interval mass for telescoping the expected-distance formula. -/
noncomputable def segment (w : Nat → ℝ) (a b : Nat) : ℝ := ∑ k ∈ Finset.Ico a b, w k

theorem segment_single (w : Nat → ℝ) (a : Nat) : segment w a (a + 1) = w a := by
  simp [segment]

theorem segment_concat (w : Nat → ℝ) (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    segment w a b + segment w b c = segment w a c :=
  Finset.sum_Ico_consecutive _ hab hbc

theorem segment_pos (w : Nat → ℝ) (a b : Nat) (hab : a < b)
    (hw : ∀ k ∈ Finset.Ico a b, 0 < w k) : 0 < segment w a b :=
  Finset.sum_pos hw (Finset.nonempty_Ico.mpr hab)

theorem segment_nonneg (w : Nat → ℝ) (a b : Nat)
    (hw : ∀ k ∈ Finset.Ico a b, 0 ≤ w k) : 0 ≤ segment w a b := Finset.sum_nonneg hw

theorem segment_first (w : Nat → ℝ) (a b : Nat) (hab : a < b) :
    w a + segment w (a + 1) b = segment w a b := by
  simpa only [segment_single] using segment_concat w a (a + 1) b (by omega) (by omega)

theorem segment_last (w : Nat → ℝ) (a b : Nat) (hab : a ≤ b) :
    segment w a b + w b = segment w a (b + 1) := by
  simpa only [segment_single] using segment_concat w a b (b + 1) hab (by omega)

/-- Growth of the interval from its left endpoint. -/
theorem interior_forward (w : Nat → ℝ) (x y : Nat) (hxy : x ≤ y)
    (hw : ∀ k ∈ Finset.Ico x (y + 1), 0 < w k) :
    ∑ a ∈ Finset.Ico x (y + 1), w a / segment w x (a + 1) ≤
      1 + Real.log (segment w x (y + 1)) - Real.log (w x) := by
  have hx : 0 < w x := hw x (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have h := sum_le_rise (fun a => w a / segment w x (a + 1))
    (fun a => Real.log (segment w x a)) (x + 1) (y + 1) (by omega) (by
      intro a ha
      obtain ⟨ha, ha'⟩ := Finset.mem_Ico.mp ha
      have hpos := segment_pos w x a (by omega) (by
        intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
      have hwa : 0 ≤ w a := le_of_lt (hw a (Finset.mem_Ico.mpr ⟨by omega, by omega⟩))
      have step := ratio_step (segment w x a) (w a) hpos hwa
      rwa [segment_last w x a (by omega)] at step)
  have split := segment_concat (fun a => w a / segment w x (a + 1)) x (x + 1) (y + 1)
    (by omega) (by omega)
  simp only [segment_single, div_self hx.ne'] at split
  simp only [segment_single] at h
  change 1 + (∑ a ∈ Finset.Ico (x + 1) (y + 1), w a / segment w x (a + 1)) =
    ∑ a ∈ Finset.Ico x (y + 1), w a / segment w x (a + 1) at split
  linarith

/-- Growth of the interval from its right endpoint. -/
theorem interior_backward (w : Nat → ℝ) (x y : Nat) (hxy : x ≤ y)
    (hw : ∀ k ∈ Finset.Ico x (y + 1), 0 < w k) :
    ∑ a ∈ Finset.Ico x (y + 1), w a / segment w a (y + 1) ≤
      1 + Real.log (segment w x (y + 1)) - Real.log (w y) := by
  have hy : 0 < w y := hw y (Finset.mem_Ico.mpr ⟨hxy, by omega⟩)
  have h := sum_le_fall (fun a => w a / segment w a (y + 1))
    (fun a => Real.log (segment w a (y + 1))) x y hxy (by
      intro a ha
      obtain ⟨ha, ha'⟩ := Finset.mem_Ico.mp ha
      have hpos := segment_pos w (a + 1) (y + 1) (by omega) (by
        intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
      have hwa : 0 ≤ w a := le_of_lt (hw a (Finset.mem_Ico.mpr ⟨ha, by omega⟩))
      have step := ratio_step (segment w (a + 1) (y + 1)) (w a) hpos hwa
      have he := segment_first w a (y + 1) (by omega)
      rw [add_comm (w a)] at he
      rwa [he] at step)
  have split := segment_last (fun a => w a / segment w a (y + 1)) x y hxy
  simp only [segment_single, div_self hy.ne'] at split h
  change (∑ a ∈ Finset.Ico x y, w a / segment w a (y + 1)) + 1 =
    ∑ a ∈ Finset.Ico x (y + 1), w a / segment w a (y + 1) at split
  linarith

end RotationBST.LazyFinger.RandomAnalysis
