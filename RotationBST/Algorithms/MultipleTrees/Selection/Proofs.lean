module

public import RotationBST.Algorithms.MultipleTrees.Selection.Definitions.Abstract
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.MultipleTrees

theorem ranking_perm (n : Nat) (frequency : Nat → Nat) : (ranking n frequency).Perm (List.range n) :=
  List.mergeSort_perm _ _

theorem ranking_sorted (n : Nat) (frequency : Nat → Nat) :
    (ranking n frequency).Pairwise (fun a b => frequency b ≤ frequency a) := by
  have sorted := List.pairwise_mergeSort
    (le := fun a b : Nat => decide (frequency b ≤ frequency a))
    (by intro a b c first last; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (List.range n)
  simpa only [ranking, decide_eq_true_eq] using sorted

theorem selected_length (n capacity : Nat) (frequency : Nat → Nat) :
    (selected n capacity frequency).length = min capacity n := by
  simp only [selected, List.length_take, (ranking_perm n frequency).length_eq, List.length_range]

theorem selected_distinct (n capacity : Nat) (frequency : Nat → Nat) :
    (selected n capacity frequency).Nodup :=
  ((ranking_perm n frequency).nodup_iff.mpr List.nodup_range).take

theorem selected_valid (n capacity : Nat) (frequency : Nat → Nat) :
    ∀ x ∈ selected n capacity frequency, x < n := by
  intro x member
  exact List.mem_range.mp ((ranking_perm n frequency).mem_iff.mp (List.mem_of_mem_take member))

/-- Every stored key is at least as frequent as every omitted universe key. -/
theorem selected_dominates (n capacity : Nat) (frequency : Nat → Nat) (x y : Nat)
    (stored : x ∈ selected n capacity frequency) (valid : y < n)
    (omitted : y ∉ selected n capacity frequency) : frequency y ≤ frequency x := by
  have member : y ∈ ranking n frequency := (ranking_perm n frequency).mem_iff.mpr (List.mem_range.mpr valid)
  have suffix : y ∈ (ranking n frequency).drop capacity := by
    rw [← List.take_append_drop capacity (ranking n frequency), List.mem_append] at member
    exact member.resolve_left omitted
  have sorted := ranking_sorted n frequency
  rw [← List.take_append_drop capacity (ranking n frequency), List.pairwise_append] at sorted
  exact sorted.2.2 x stored y suffix

theorem selected_mass_le (n capacity : Nat) (frequency : Nat → Nat) :
    ((selected n capacity frequency).map frequency).sum ≤ ((List.range n).map frequency).sum := by
  have split : ((selected n capacity frequency).map frequency).sum +
      (((ranking n frequency).drop capacity).map frequency).sum = ((ranking n frequency).map frequency).sum := by
    rw [← List.sum_append, ← List.map_append, selected, List.take_append_drop]
  have total := ((ranking_perm n frequency).map frequency).sum_eq
  omega

/-- Omitting a key from the `capacity` most frequent choices certifies at least
that much reciprocal probability. This is the miss-cost lower bound in the
multiple-tree construction of arXiv:1304.6897, Theorem 9. -/
theorem omitted_frequency (n capacity : Nat) (frequency : Nat → Nat) (y : Nat)
    (fits : capacity ≤ n) (valid : y < n) (omitted : y ∉ selected n capacity frequency) :
    capacity * frequency y ≤ ((List.range n).map frequency).sum := by
  have dominated := selected_dominates n capacity frequency
  have lower (xs : List Nat) (all : ∀ x ∈ xs, frequency y ≤ frequency x) :
      xs.length * frequency y ≤ (xs.map frequency).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have first := all x (by simp)
      have rest := ih (by intro z hz; exact all z (by simp [hz]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      nlinarith
  have bound := lower (selected n capacity frequency) (fun x hx => dominated x y hx valid omitted)
  rw [selected_length, Nat.min_eq_left fits] at bound
  exact bound.trans (selected_mass_le n capacity frequency)

/-- A missed positive-frequency key has information content at least the
logarithm of the number of stored successors. -/
theorem omitted_information (n capacity : Nat) (frequency : Nat → Nat) (y : Nat)
    (fits : capacity ≤ n) (nonempty : 0 < capacity) (valid : y < n)
    (omitted : y ∉ selected n capacity frequency) (positive : 0 < frequency y) :
    Real.logb 2 capacity ≤ Real.logb 2 ((((List.range n).map frequency).sum : ℝ) / frequency y) := by
  have mass := omitted_frequency n capacity frequency y fits valid omitted
  have frequencyPositive : (0 : ℝ) < frequency y := by exact_mod_cast positive
  have ratio : (capacity : ℝ) ≤ (((List.range n).map frequency).sum : ℝ) / frequency y := by
    apply (le_div_iff₀ frequencyPositive).mpr
    exact_mod_cast mass
  exact Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast nonempty) ratio

end RotationBST.MultipleTrees
