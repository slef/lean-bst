module

public import RotationBST.Bounds.LazyFinger.Random.Intervals
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger.RandomAnalysis

theorem exterior_left (w : Nat → ℝ) (lo x y : Nat) (hlo : lo ≤ x) (hxy : x ≤ y)
    (hw : ∀ k ∈ Finset.Ico lo (y + 1), 0 < w k) :
    ∑ a ∈ Finset.Ico lo x, (w a / segment w a (x + 1) - w a / segment w a (y + 1)) ≤
      Real.log (segment w x (y + 1)) - Real.log (w x) := by
  have hc : 0 ≤ segment w (x + 1) (y + 1) := segment_nonneg _ _ _ (by
    intro k hk; apply le_of_lt (hw k ?_); simp only [Finset.mem_Ico] at *; omega)
  have h := sum_le_rise
    (fun a => w a / segment w a (x + 1) - w a / segment w a (y + 1))
    (fun a => Real.log (segment w a (y + 1)) - Real.log (segment w a (x + 1))) lo x hlo (by
      intro a ha
      obtain ⟨ha, ha'⟩ := Finset.mem_Ico.mp ha
      have hp : 0 < segment w (a + 1) (x + 1) := segment_pos _ _ _ (by omega) (by
        intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
      have hb : 0 ≤ w a := le_of_lt (hw a (Finset.mem_Ico.mpr ⟨ha, by omega⟩))
      have step := difference_step (segment w (a + 1) (x + 1)) (w a)
        (segment w (x + 1) (y + 1)) hp hb hc
      have he : segment w (a + 1) (x + 1) + w a = segment w a (x + 1) := by
        linarith [segment_first w a (x + 1) (by omega)]
      rwa [he, segment_concat w a (x + 1) (y + 1) (by omega) (by omega),
        segment_concat w (a + 1) (x + 1) (y + 1) (by omega) (by omega)] at step)
  have hp : 0 < segment w lo (x + 1) := segment_pos _ _ _ (by omega) (by
    intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
  have hm : segment w lo (x + 1) ≤ segment w lo (y + 1) := by
    linarith [segment_concat w lo (x + 1) (y + 1) (by omega) (by omega)]
  have hlog := Real.log_le_log hp hm
  simp only [segment_single] at h
  linarith

theorem exterior_right (w : Nat → ℝ) (x y hi : Nat) (hxy : x ≤ y) (hhi : y < hi)
    (hw : ∀ k ∈ Finset.Ico x hi, 0 < w k) :
    ∑ a ∈ Finset.Ico (y + 1) hi, (w a / segment w y (a + 1) - w a / segment w x (a + 1)) ≤
      Real.log (segment w x (y + 1)) - Real.log (w y) := by
  have hc : 0 ≤ segment w x y := segment_nonneg _ _ _ (by
    intro k hk; apply le_of_lt (hw k ?_); simp only [Finset.mem_Ico] at *; omega)
  have h := sum_le_fall
    (fun a => w a / segment w y (a + 1) - w a / segment w x (a + 1))
    (fun a => Real.log (segment w x a) - Real.log (segment w y a)) (y + 1) hi (by omega) (by
      intro a ha
      obtain ⟨ha, ha'⟩ := Finset.mem_Ico.mp ha
      have hp : 0 < segment w y a := segment_pos _ _ _ (by omega) (by
        intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
      have hb : 0 ≤ w a := le_of_lt (hw a (Finset.mem_Ico.mpr ⟨by omega, ha'⟩))
      have step := difference_step (segment w y a) (w a) (segment w x y) hp hb hc
      have he : segment w y a + segment w x y = segment w x a := by
        linarith [segment_concat w x y a hxy (by omega)]
      have he' : segment w y (a + 1) + segment w x y = segment w x (a + 1) := by
        linarith [segment_concat w x y (a + 1) hxy (by omega)]
      rwa [segment_last w y a (by omega), he, he'] at step)
  have hp : 0 < segment w y hi := segment_pos _ _ _ hhi (by
    intro k hk; apply hw k; simp only [Finset.mem_Ico] at *; omega)
  have hm : segment w y hi ≤ segment w x hi := by
    linarith [segment_concat w x y hi hxy (by omega)]
  have hlog := Real.log_le_log hp hm
  simp only [segment_single] at h
  linarith

end RotationBST.LazyFinger.RandomAnalysis
