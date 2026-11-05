module

public import RotationBST.Algorithms.MultipleTrees.Tradeoff
public import RotationBST.Bounds.ConditionalEntropy.Transitions
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

/-- Compose the actual requests in a fixed preprocessed store. Frequencies may
come from a larger sequence; domination ensures every performed transition
has positive frequency in the fixed query bound. -/
theorem sequence_fixed (n capacity : Nat) (positive : 0 < n) (frequency : Nat → Nat → Nat)
    (nonempty : 0 < capacity) (fits : capacity ≤ n) (p : Fin n) (xs : List (Fin n))
    (covers : ∀ a b, LazyFinger.frequency p (xs.map Fin.val) a b ≤ frequency a b) :
    ∃ q k, LinkedSearch.Execution (build n capacity positive frequency) p (xs.map Fin.val) q k ∧
      (k : ℝ) ≤ 6 * ((xs.length : ℝ) + ConditionalEntropy.transitionSum
        (fun a b => Real.logb 2 ((ConditionalEntropy.rowTotal n frequency a : ℝ) / frequency a b))
        p (xs.map Fin.val)) * (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) := by
  induction xs generalizing p with
  | nil => exact ⟨p, 0, .nil, by simp [ConditionalEntropy.transitionSum]⟩
  | cons x xs ih =>
    have first : 0 < frequency p x := by
      have bound := covers p x
      simp only [List.map_cons, LazyFinger.frequency, and_self, ↓reduceIte] at bound
      omega
    have rest : ∀ a b, LazyFinger.frequency x (xs.map Fin.val) a b ≤ frequency a b := by
      intro a b
      have bound := covers a b
      simp only [List.map_cons, LazyFinger.frequency] at bound
      omega
    obtain ⟨q, k, execution, cost⟩ := ih x rest
    let firstCost := (LinkedSearch.request (build n capacity positive frequency) p x).2
    refine ⟨q, firstCost + k, .cons (request_execution n capacity positive frequency p x) execution, ?_⟩
    have bound := request_tradeoff n capacity positive frequency nonempty fits p x first
    have combined := add_le_add bound cost
    rw [Nat.cast_add]
    calc
      (firstCost : ℝ) + k ≤ _ := combined
      _ = _ := by simp only [List.length_cons, List.map_cons, ConditionalEntropy.transitionSum, Nat.cast_add, Nat.cast_one]; ring

/-- The complete multiple-tree tradeoff, with the empirical transition matrix
used only during preprocessing. It gives a legal linked-pointer execution,
linear-in-capacity storage, and normalized conditional-information time. -/
theorem sequence_tradeoff (n capacity : Nat) (positive : 0 < n)
    (nonempty : 0 < capacity) (fits : capacity ≤ n) (p : Fin n) (xs : List (Fin n)) :
    ∃ q k,
      LinkedSearch.Execution (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val)))
        p (xs.map Fin.val) q k ∧
      (k : ℝ) ≤ 6 * ConditionalEntropy.cost n p (xs.map Fin.val) *
        (1 + Real.logb 2 n) / (1 + Real.logb 2 capacity) ∧
      (build n capacity positive (LazyFinger.frequency p (xs.map Fin.val))).words ≤ 10 * n * capacity := by
  obtain ⟨q, k, execution, cost⟩ := sequence_fixed n capacity positive
    (LazyFinger.frequency p (xs.map Fin.val)) nonempty fits p xs (fun _ _ => le_rfl)
  have valid : ∀ x ∈ xs.map Fin.val, x < n := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.isLt
  rw [ConditionalEntropy.sequenceInformation_transitions n p (xs.map Fin.val) p.isLt valid] at cost
  refine ⟨q, k, execution, ?_, build_space n capacity positive _ nonempty⟩
  simpa only [ConditionalEntropy.cost, List.length_map] using cost

end RotationBST.MultipleTrees
