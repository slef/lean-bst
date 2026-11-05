module

public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.Distance
public import RotationBST.Algorithms.GreedyASS.Virgin.History
public import RotationBST.Algorithms.GreedyASS.Barrier.Streams
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- No later point can lie between an active point and either of its
nearest same-row neighbors in an ASS snapshot. -/
theorem newer_outside {P : Finset Point} (satisfied : ASS P) {q p : Point}
    (active : Active P q) {a b : Nat} (left : leftNeighbor P q = some a)
    (right : rightNeighbor P q = some b) (member : p ∈ P) (newer : q.2 < p.2) :
    p.1 ≤ a ∨ b ≤ p.1 := by
  have ha := (left_spec P q a).mp left
  have hb := (right_spec P q b).mp right
  by_contra outside
  have inner : a < p.1 ∧ p.1 < b := by omega
  have different : q.1 ≠ p.1 := by
    intro equal
    have := active.2 p member equal.symm
    omega
  obtain ⟨w, hw, distinct, _, rect, side⟩ := side_witness satisfied
    active.1 member different (by omega)
  unfold Rectangle at rect
  apply distinct
  rcases side with column | sameRow
  · have bound := active.2 w hw column
    exact Prod.ext column (by omega)
  · have innerW : a < w.1 ∧ w.1 < b := by omega
    have rowMember : (w.1, q.2) ∈ P := by simpa only [← sameRow, Prod.mk.eta] using hw
    have xEqual : w.1 = q.1 := by
      by_contra unequal
      rcases lt_or_gt_of_ne unequal with low | high
      · have := ha.2.2 w.1 rowMember low
        omega
      · have := hb.2.2 w.1 rowMember high
        omega
    exact Prod.ext xEqual sameRow

/-- Future rows never add points below the starting time. -/
theorem fill_old (step : Nat → Nat → Finset Point → Finset Nat)
    (time : Nat) (P : Finset Point) (xs : List Nat) {p : Point} (old : p.2 < time) :
    p ∈ fill step time P xs ↔ p ∈ P := by
  induction xs generalizing time P with
  | nil => rfl
  | cons x xs ih =>
    rw [fill, ih (time + 1) _ (by omega)]
    have absent : p ∉ row time (step time x P) := by
      intro hp
      have := ((mem_row p time _).mp hp).2
      omega
    simp only [Finset.mem_union, absent, or_false]

/-- Every request occurs as an actual point at or after the initial time. -/
theorem search_point (time : Nat) (P : Finset Point) (xs : List Nat) {x : Nat}
    (member : x ∈ xs) : ∃ stamp, time ≤ stamp ∧ (x, stamp) ∈ fill greedySweep time P xs := by
  induction xs generalizing time P with
  | nil => simp at member
  | cons y ys ih =>
    rcases List.mem_cons.mp member with rfl | later
    · refine ⟨time, le_rfl, ?_⟩
      apply fill_mono greedySweep (time + 1) (P ∪ row time (greedySweep time x P)) ys
      exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨Finset.mem_insert_self _ _, rfl⟩)
    · obtain ⟨stamp, lower, point⟩ := ih (time + 1) (P ∪ row time (greedySweep time y P)) later
      exact ⟨stamp, by omega, point⟩

/-- An item that is internal after a suffix has searches on both sides
since its last access. Otherwise the access barrier keeps it glancing. -/
theorem internal_searches {n stamp x : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P) (accessed : (x, stamp) ∈ P)
    (internal : Internal (fill greedySweep (stamp + 1) P xs) (x, stamp)) :
    (∃ a ∈ xs, a < x) ∧ (∃ b ∈ xs, x < b) := by
  constructor
  · by_contra noSearch
    have side : ∀ a ∈ xs, x ≤ a := by
      intro a ha
      by_contra lower
      exact noSearch ⟨a, ha, by omega⟩
    have barrier := Barrier.no_left_access xs history accessed side
    apply internal.2.2
    left
    refine ⟨internal.1, internal.2.1, ?_⟩
    intro p hp recent
    have bound := barrier p hp recent
    have unequal : p.1 ≠ x := by
      intro equal
      have := internal.1.2 p hp equal
      omega
    omega
  · by_contra noSearch
    have side : ∀ b ∈ xs, b ≤ x := by
      intro b hb
      by_contra upper
      exact noSearch ⟨b, hb, by omega⟩
    have barrier := Barrier.no_right_access xs history accessed side
    apply internal.2.2
    right
    refine ⟨internal.1, internal.2.1, ?_⟩
    intro p hp recent
    have bound := barrier p hp recent
    have unequal : p.1 ≠ x := by
      intro equal
      have := internal.1.2 p hp equal
      omega
    omega

/-- The recent search history of an internal item brackets both of its
same-row neighbors. The searches are obtained from the actual execution,
not assumed as an additional geometric condition. -/
theorem internal_bracket (searches : List Nat) {n x stamp a b : Nat}
    (valid : ∀ y ∈ searches, y < n)
    (internal : Internal (Virgin.points searches) (x, stamp))
    (left : leftNeighbor (Virgin.points searches) (x, stamp) = some a)
    (right : rightNeighbor (Virgin.points searches) (x, stamp) = some b) :
    ∃ u ∈ searches.drop stamp, ∃ v ∈ searches.drop stamp, u ≤ a ∧ b ≤ v := by
  have history := Virgin.points_history n searches valid
  have age := (history (x, stamp) internal.1.1).2
  have prefixLength : (searches.take (stamp + 1)).length = stamp + 1 := by
    simp only [List.length_take, Nat.min_eq_left (by omega : stamp + 1 ≤ searches.length)]
  have split : Virgin.points searches = fill greedySweep (stamp + 1)
      (Virgin.points (searches.take (stamp + 1))) (searches.drop (stamp + 1)) := by
    calc
      Virgin.points searches = Virgin.points
          (searches.take (stamp + 1) ++ searches.drop (stamp + 1)) := by
        rw [List.take_append_drop]
      _ = _ := by rw [Virgin.points_append, prefixLength]
  have prefixHistory : History n (stamp + 1) (Virgin.points (searches.take (stamp + 1))) := by
    simpa only [prefixLength] using Virgin.points_history n (searches.take (stamp + 1))
      (fun y hy => valid y (List.mem_of_mem_take hy))
  have continued : Internal (fill greedySweep (stamp + 1)
      (Virgin.points (searches.take (stamp + 1))) (searches.drop (stamp + 1))) (x, stamp) := by
    rw [← split]
    exact internal
  have accessed : (x, stamp) ∈ Virgin.points (searches.take (stamp + 1)) :=
    (fill_old greedySweep (stamp + 1) _ _ (p := (x, stamp)) (by omega)).mp continued.1.1
  obtain ⟨⟨u, hu, ux⟩, ⟨v, hv, xv⟩⟩ := internal_searches _ prefixHistory accessed continued
  have satisfied : ASS (Virgin.points searches) := by
    have run := fill_spec (greedyASS n) 0 ∅ searches
      (by simp [History]) ass_empty valid
    simpa only [Virgin.points, greedyASS] using run.1
  obtain ⟨ut, timeU, pointU⟩ := search_point (stamp + 1)
    (Virgin.points (searches.take (stamp + 1))) _ hu
  obtain ⟨vt, timeV, pointV⟩ := search_point (stamp + 1)
    (Virgin.points (searches.take (stamp + 1))) _ hv
  rw [← split] at pointU pointV
  have outerU := newer_outside satisfied internal.1 left right pointU (by omega)
  have outerV := newer_outside satisfied internal.1 left right pointV (by omega)
  have ax := ((left_spec _ _ a).mp left).2.1
  have xb := ((right_spec _ _ b).mp right).2.1
  exact ⟨u, List.drop_subset_drop_left searches (by omega) hu,
    v, List.drop_subset_drop_left searches (by omega) hv, by omega, by omega⟩

/-- Greedy projections introduce no key that was absent both from the
initial point set and from the request stream. -/
theorem fill_property (property : Nat → Prop) (time : Nat) (P : Finset Point) (xs : List Nat)
    (initial : ∀ p ∈ P, property p.1) (valid : ∀ x ∈ xs, property x) :
    ∀ p ∈ fill greedySweep time P xs, property p.1 := by
  induction xs generalizing time P with
  | nil => exact initial
  | cons x xs ih =>
    apply ih (time + 1) (P ∪ row time (greedySweep time x P))
    · intro p hp
      rcases Finset.mem_union.mp hp with old | added
      · exact initial p old
      · have member := ((mem_row p time _).mp added).1
        rcases Finset.mem_insert.mp member with searched | projected
        · rw [searched]
          exact valid x (List.mem_cons_self ..)
        · obtain ⟨q, hq, same⟩ := Finset.mem_image.mp projected
          rw [← same]
          exact initial q (Finset.mem_filter.mp hq).1
    · exact fun y hy => valid y (List.mem_cons_of_mem _ hy)

theorem points_property (property : Nat → Prop) (xs : List Nat)
    (valid : ∀ x ∈ xs, property x) : ∀ p ∈ Virgin.points xs, property p.1 :=
  fill_property property 0 ∅ xs (by simp) valid

theorem points_satisfied (xs : List Nat) {n : Nat} (valid : ∀ x ∈ xs, x < n) :
    ASS (Virgin.points xs) := by
  have run := fill_spec (greedyASS n) 0 ∅ xs
    (by simp [History]) ass_empty valid
  simpa only [Virgin.points, greedyASS] using run.1

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
