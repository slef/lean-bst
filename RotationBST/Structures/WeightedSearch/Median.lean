module

public import RotationBST.Structures.WeightedSearch.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedSearch

/-- The located index straddles the chosen cumulative unit of weight. -/
theorem locate_spec (weights : List Nat) (target : Nat) (valid : target < weights.sum) :
    locate weights target < weights.length ∧
      (weights.take (locate weights target)).sum ≤ target ∧
      target < (weights.take (locate weights target + 1)).sum := by
  induction weights generalizing target with
  | nil => simp at valid
  | cons w ws ih =>
    by_cases first : target < w
    · simp [locate, first]
    · have tailValid : target - w < ws.sum := by simp only [List.sum_cons] at valid; omega
      obtain ⟨index, before, after⟩ := ih _ tailValid
      simp only [locate, first, ↓reduceIte, List.length_cons]
      rw [show 1 + locate ws (target - w) = locate ws (target - w) + 1 by omega]
      simp only [List.take_succ_cons, List.sum_cons]
      omega

theorem pivot_lt (weights : List Nat) (nonempty : weights ≠ []) : pivot weights < weights.length := by
  unfold pivot
  split
  · exact List.length_pos_iff.mpr nonempty
  · rename_i positive
    exact (locate_spec weights _ (Nat.div_lt_self (Nat.pos_of_ne_zero positive) (by omega))).1

private theorem sum_split (weights : List Nat) (k : Nat) :
    (weights.take k).sum + (weights.drop k).sum = weights.sum := by
  rw [← List.sum_append, List.take_append_drop]

/-- Removing the weighted median leaves each child's mass at most half of the
parent's mass. The result includes zero-weight lists and empty child intervals. -/
theorem pivot_halves (weights : List Nat) :
    2 * (weights.take (pivot weights)).sum ≤ weights.sum ∧
      2 * (weights.drop (pivot weights + 1)).sum ≤ weights.sum := by
  by_cases zero : weights.sum = 0
  · have left := sum_split weights (pivot weights)
    have right := sum_split weights (pivot weights + 1)
    omega
  · have valid : weights.sum / 2 < weights.sum := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by omega)
    have position := locate_spec weights _ valid
    have total := sum_split weights (locate weights (weights.sum / 2) + 1)
    simp only [pivot, zero, ↓reduceIte]
    omega

end RotationBST.WeightedSearch
