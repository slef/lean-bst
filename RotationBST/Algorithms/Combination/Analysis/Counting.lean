module

public import RotationBST.Algorithms.Combination.Rounds.Charges
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Analysis

/-- Removing the initial span loses at most one selected-worker round. -/
theorem count_tail (side : Bool) (rounds : List Rounds.Span) :
    Rounds.count side rounds ≤ Rounds.count side rounds.tail + 1 := by
  cases rounds with
  | nil => simp [Rounds.count]
  | cons span rest =>
    by_cases same : span.side = side <;>
      simp [Rounds.count, same]

/-- Removing the final span loses at most one span of either selected worker. -/
theorem count_dropLast (side : Bool) (rounds : List Rounds.Span) :
    Rounds.count side rounds ≤ Rounds.count side rounds.dropLast + 1 := by
  induction rounds using List.twoStepInduction with
  | nil => simp [Rounds.count]
  | singleton span => by_cases same : span.side = side <;> simp [Rounds.count, same]
  | cons_cons a b rest ih ihTail =>
    have tail := ihTail b
    simp only [List.dropLast_cons_cons, Rounds.count, List.filter_cons] at tail ⊢
    split
    · simp only [List.length_cons]
      omega
    · exact tail

/-- Summing a uniform lower bound over selected spans. -/
theorem sum_span_bound (selected : Bool) (weights : Nat → ℝ) (rounds : List Rounds.Span) (amount factor : ℝ)
    (bounds : ∀ span ∈ rounds, span.side = selected → amount ≤ factor * span.charge weights) :
    (Rounds.count selected rounds : ℝ) * amount ≤ factor * Rounds.charge selected weights rounds := by
  induction rounds with
  | nil => simp [Rounds.count, Rounds.charge]
  | cons span rest ih =>
    have tail := ih (fun other member => bounds other (List.mem_cons_of_mem _ member))
    by_cases same : span.side = selected
    · have head := bounds span (List.mem_cons_self ..) same
      simp only [Rounds.count, Rounds.charge, List.filter_cons, same, beq_self_eq_true, ↓reduceIte,
        List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons] at tail ⊢
      nlinarith
    · simp only [Rounds.count, Rounds.charge, List.filter_cons, beq_iff_eq, same,
        ↓reduceIte] at tail ⊢
      exact tail

end RotationBST.Combo.Analysis
