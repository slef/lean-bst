module

public import RotationBST.Structures.WeightedSearch.Abstract
public import RotationBST.Bounds.Implications.WeightedEntropy
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.StaticTree
open RotationBST.Tree (depth)

/-- A weighted-median tree realizes the frequency-entropy upper bound. Keys
with zero frequency remain in the tree; no positivity assumption is needed
for keys that never occur in the request sequence. -/
theorem entropy_tree (n : Nat) (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ t : Tree, t.size = n ∧ (cost t xs : ℝ) ≤ Bounds.staticCost n xs := by
  let weights := (List.range n).map xs.count
  let t := WeightedSearch.build weights
  have length : weights.length = n := by simp [weights]
  have size : t.size = n := (WeightedSearch.Results.size weights).trans length
  have total : (weights.sum : ℝ) = xs.length := by
    have counts := Bounds.sum_count n xs valid
    have sums := List.sum_toFinset (fun x => (xs.count x : ℝ)) (l := List.range n) List.nodup_range
    simp only [List.toFinset_range] at sums
    rw [sums] at counts
    simpa [weights, Nat.cast_list_sum, List.map_map, Function.comp_def] using counts
  have depth (x : Nat) (member : x ∈ xs) :
      (depth t x : ℝ) ≤ Real.logb 2 ((xs.length : ℝ) / xs.count x) := by
    have index : x < weights.length := by rw [length]; exact valid x member
    have atIndex : weights[x] = xs.count x := by simp [weights]
    have positive : 0 < weights[x] := by rw [atIndex]; exact List.count_pos_iff.mpr member
    have bound := WeightedSearch.Results.depth weights x index positive
    simpa only [total, atIndex] using bound
  have form : Bounds.staticCost n xs =
      (xs.map fun x => 1 + Real.logb 2 ((xs.length : ℝ) / xs.count x)).sum := by
    rw [Bounds.staticCost, Bounds.sum_count_mul n xs _ valid, List.sum_map_add]
    simp
  refine ⟨t, size, ?_⟩
  rw [form]
  have sumBound (ys : List Nat) (members : ∀ x ∈ ys, x ∈ xs) :
      (cost t ys : ℝ) ≤ (ys.map fun x => 1 + Real.logb 2 ((xs.length : ℝ) / xs.count x)).sum := by
    induction ys with
    | nil => simp [cost]
    | cons y ys ih =>
      have first := depth y (members y (by simp))
      have tail := ih (fun x hx => members x (by simp [hx]))
      simp only [cost, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one] at tail ⊢
      linarith
  exact sumBound xs (fun _ member => member)

end RotationBST.StaticTree
