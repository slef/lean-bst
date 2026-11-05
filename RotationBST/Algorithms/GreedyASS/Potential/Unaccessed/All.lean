module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Purple
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- Every untouched active point has nonincreasing selected potential. -/
theorem all_value (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) {q : Point}
    (active : Active (Virgin.points searches) q) (untouched : q.1 ∉ Virgin.keys searches searched) :
    value t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) q ≤
      value t lo (searches ++ [searched]) (Virgin.points searches) q := by
  by_cases external : External (Virgin.points searches) q
  · have oldValid : ∀ y ∈ searches, y < n := fun y hy => valid y (List.mem_append_left _ hy)
    have history := Virgin.points_history n searches oldValid
    have satisfied : ASS (Virgin.points searches) := by
      have run := fill_spec (greedyASS n) 0 ∅ searches
        (by simp [History]) ass_empty oldValid
      simpa only [Virgin.points, greedyASS] using run.1
    rw [Virgin.points_snoc]
    exact external_value t lo (searches ++ [searched]) satisfied history external untouched
  · exact nonexternal_value t lo searches searched valid active external untouched

/-- All untouched columns are included, even ones not yet present in the
point set. The latter keep zero amount without an artificial old color. -/
theorem all_amount (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) {x : Nat}
    (untouched : x ∉ Virgin.keys searches searched) :
    itemAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) x ≤
      itemAmount t lo (searches ++ [searched]) (Virgin.points searches) x := by
  cases recent : latest (Virgin.points searches) x with
  | none =>
    rw [Virgin.points_snoc]
    simp only [itemAmount, itemValue, latest_unchanged _ _ _ x untouched, recent]
    exact le_rfl
  | some stamp =>
    have active := (latest_spec _ x stamp).mp recent
    have newActive : Active (Virgin.points (searches ++ [searched])) (x, stamp) := by
      rw [Virgin.points_snoc]
      exact (active_unchanged _ _ _ (x, stamp) untouched).mpr active
    have bound := all_value t lo searches searched valid active untouched
    rw [← (item_spec t lo (searches ++ [searched]) newActive).2,
      ← (item_spec t lo (searches ++ [searched]) active).2,
      Accessed.amount_exact, Accessed.amount_exact] at bound
    exact WithTop.coe_le_coe.mp bound

/-- The complete unaccessed contribution to Phase II is nonpositive. -/
theorem all_total (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) (keys : Finset Nat)
    (untouched : ∀ x ∈ keys, x ∉ Virgin.keys searches searched) :
    totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) keys ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) keys := by
  unfold totalAmount
  exact Finset.sum_le_sum (fun x hx => all_amount t lo searches searched valid (untouched x hx))

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
