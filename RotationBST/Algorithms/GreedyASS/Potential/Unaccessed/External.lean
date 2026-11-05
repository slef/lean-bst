module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Neighbors
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- Green is monotone under addition of a later row lying entirely on one
side of the item. Missing old neighbors give infinity and need no exception. -/
theorem green_mono (t : Tree) (lo : Nat) {n time : Nat} {P : Finset Point}
    (keys : Finset Nat) (history : History n time P) (x : Nat)
    (side : (∀ y ∈ keys, y < x) ∨ (∀ y ∈ keys, x < y)) :
    green t lo (P ∪ row time keys) x ≤ green t lo P x := by
  cases left : leftExternal P x with
  | none => simp [green, left]
  | some a =>
    cases right : rightExternal P x with
    | none => simp [green, left, right]
    | some b =>
      obtain ⟨u, v, newLeft, newRight, au, ux, xv, vb⟩ := neighbors_nested keys history left right side
      have distance := Distance.enclosing t lo x a u v b au (by omega) vb
      simp only [green, left, right, newLeft, newRight]
      exact WithTop.coe_le_coe.mpr (Nat.add_le_add_right distance 1)

/-- Lemma 3.13 at point level. Both non-corner minimum potentials and old
top corners are covered using the actual snapshot corner test. -/
theorem external_value (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    {q : Point} (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    value t lo searches (P ∪ row time (greedySweep time searched P)) q ≤
      value t lo searches P q := by
  let keys := greedySweep time searched P
  have active := external.elim (fun h => h.1) (fun h => h.1)
  have newExternal := (external_unchanged keys history active untouched).mpr external
  have greenBound := green_mono t lo keys history q.1 (one_side satisfied history external untouched)
  rw [(external_spec t lo searches newExternal).2, (external_spec t lo searches external).2]
  by_cases latest : LatestRow P q.2
  · rw [ite_eq_left latest]
    split
    · exact le_rfl
    · exact min_le_right _ _
  · have notNew : ¬ LatestRow (P ∪ row time keys) q.2 := by
      intro newer
      exact latest (fun p hp => newer p (Finset.mem_union_left _ hp))
    rw [ite_eq_right latest, ite_eq_right notNew]
    exact min_le_min greenBound le_rfl

/-- Natural-valued item form of Lemma 3.13. The latest old point remains
the latest point in its column, so the comparison uses the actual item query. -/
theorem external_amount (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    {q : Point} (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    itemAmount t lo searches (P ∪ row time (greedySweep time searched P)) q.1 ≤
      itemAmount t lo searches P q.1 := by
  have active := external.elim (fun h => h.1) (fun h => h.1)
  have newActive := (active_unchanged P time (greedySweep time searched P) q untouched).mpr active
  have bound := external_value t lo searches satisfied history external untouched
  have oldItem := (item_spec t lo searches active).2
  have newItem := (item_spec t lo searches newActive).2
  rw [← oldItem, ← newItem, Accessed.amount_exact, Accessed.amount_exact] at bound
  exact WithTop.coe_le_coe.mp bound

/-- Sum the nonincrease over any set of unaccessed old external columns. -/
theorem external_total (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    (keys : Finset Nat) (external : keys ⊆ externalKeys P)
    (untouched : ∀ x ∈ keys, x ∉ greedySweep time searched P) :
    totalAmount t lo searches (P ∪ row time (greedySweep time searched P)) keys ≤
      totalAmount t lo searches P keys := by
  unfold totalAmount
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨stamp, outside⟩ := (mem_external P x).mp (external hx)
  exact external_amount t lo searches (n := n) (time := time) (searched := searched)
    (P := P) satisfied history (q := (x, stamp)) outside (untouched x hx)

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
