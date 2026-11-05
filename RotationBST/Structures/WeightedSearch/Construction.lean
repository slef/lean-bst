module

public import RotationBST.Structures.WeightedSearch.Median
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedSearch

/-- Sufficient fuel preserves all ranks, including zero-frequency keys. -/
theorem buildFuel_size (fuel : Nat) (weights : List Nat) (enough : weights.length ≤ fuel) :
    (buildFuel fuel weights).size = weights.length := by
  induction fuel generalizing weights with
  | zero =>
    have empty : weights = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst weights
    rfl
  | succ fuel ih =>
    cases weights with
    | nil => rfl
    | cons w ws =>
      have index := pivot_lt (w :: ws) (by simp)
      have leftLength : ((w :: ws).take (pivot (w :: ws))).length = pivot (w :: ws) := by
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt index)]
      have left := ih ((w :: ws).take (pivot (w :: ws))) (by rw [leftLength]; omega)
      have right := ih ((w :: ws).drop (pivot (w :: ws) + 1)) (by
        simp only [List.length_drop]; omega)
      simp only [buildFuel, Tree.size, left, right, leftLength, List.length_drop]
      omega

/-- Every level containing a key halves the remaining mass. This exact integer
inequality is the frequency-biased search-depth guarantee before taking logs. -/
theorem buildFuel_mass (fuel : Nat) (weights : List Nat) (enough : weights.length ≤ fuel)
    (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (buildFuel fuel weights) x * weights[x] ≤ weights.sum := by
  induction fuel generalizing weights x with
  | zero => omega
  | succ fuel ih =>
    cases weights with
    | nil => simp at valid
    | cons w ws =>
      let weights := w :: ws
      let p := pivot weights
      change weights.length ≤ fuel + 1 at enough
      have index : p < weights.length := pivot_lt weights (by simp [weights])
      have leftLength : (weights.take p).length = p := by
        simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt index)]
      have leftFuel : (weights.take p).length ≤ fuel := by rw [leftLength]; exact Nat.le_of_lt_succ (lt_of_lt_of_le index enough)
      have rightFuel : (weights.drop (p + 1)).length ≤ fuel := by simp only [List.length_drop]; omega
      have leftSize := buildFuel_size fuel (weights.take p) leftFuel
      rw [leftLength] at leftSize
      have halves := pivot_halves weights
      change 2 ^ Tree.depth (.node (buildFuel fuel (weights.take p))
        (buildFuel fuel (weights.drop (p + 1)))) x * weights[x] ≤ weights.sum
      rw [Tree.depth, leftSize]
      by_cases left : x < p
      · rw [ite_eq_left left]
        have bound := ih (weights.take p) leftFuel x (by rw [leftLength]; exact left)
        simp only [List.getElem_take] at bound
        rw [pow_succ]
        change 2 * (weights.take p).sum ≤ weights.sum ∧ _ at halves
        nlinarith [halves.1]
      · rw [ite_eq_right left]
        by_cases root : x = p
        · rw [ite_eq_left root, pow_zero, one_mul]
          exact List.le_sum_of_mem (List.getElem_mem valid)
        · rw [ite_eq_right root]
          have childValid : x - p - 1 < (weights.drop (p + 1)).length := by
            simp only [List.length_drop]; change x < weights.length at valid; omega
          have bound := ih (weights.drop (p + 1)) rightFuel (x - p - 1) childValid
          have position : p + 1 + (x - p - 1) = x := by omega
          simp only [List.getElem_drop, position] at bound
          rw [pow_succ]
          change _ ∧ 2 * (weights.drop (p + 1)).sum ≤ weights.sum at halves
          nlinarith [halves.2]

theorem build_size (weights : List Nat) : (build weights).size = weights.length :=
  buildFuel_size weights.length weights le_rfl

theorem build_mass (weights : List Nat) (x : Nat) (valid : x < weights.length) :
    2 ^ Tree.depth (build weights) x * weights[x] ≤ weights.sum :=
  buildFuel_mass weights.length weights le_rfl x valid

end RotationBST.WeightedSearch
