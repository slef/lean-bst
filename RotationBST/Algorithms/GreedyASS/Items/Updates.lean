module

public import RotationBST.Algorithms.GreedyASS.Items.Geometry
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

theorem times_unchanged (P : Finset Point) (time : Nat) (keys : Finset Nat) (key : Nat)
    (untouched : key ∉ keys) : times (P ∪ row time keys) key = times P key := by
  ext stamp
  simp [mem_times, mem_row, untouched]

theorem latest_unchanged (P : Finset Point) (time : Nat) (keys : Finset Nat) (key : Nat)
    (untouched : key ∉ keys) : latest (P ∪ row time keys) key = latest P key := by
  simp only [latest, times_unchanged P time keys key untouched]

theorem old_row (P : Finset Point) (time stamp : Nat) (keys : Finset Nat) (old : stamp ≠ time) :
    keysAt (P ∪ row time keys) stamp = keysAt P stamp := by
  ext x
  simp [mem_keysAt, mem_row, old]

theorem active_unchanged (P : Finset Point) (time : Nat) (keys : Finset Nat) (q : Point)
    (untouched : q.1 ∉ keys) : Active (P ∪ row time keys) q ↔ Active P q := by
  change Active _ (q.1, q.2) ↔ Active _ (q.1, q.2)
  rw [← latest_spec, ← latest_spec, latest_unchanged P time keys q.1 untouched]

/-- Fact 3.3, both directions. The neighbors on an old access row are
unchanged; an unaccessed column also retains that same most recent access. -/
theorem neighbors_unchanged {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (member : q ∈ P) :
    leftNeighbor (P ∪ row time keys) q = leftNeighbor P q ∧
      rightNeighbor (P ∪ row time keys) q = rightNeighbor P q := by
  have old : q.2 ≠ time := Nat.ne_of_lt (history q member).2
  simp only [leftNeighbor, rightNeighbor, old_row P time q.2 keys old, and_self]

theorem external_unchanged {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (active : Active P q) (untouched : q.1 ∉ keys) :
    External (P ∪ row time keys) q ↔ External P q := by
  have current := (active_unchanged P time keys q untouched).mpr active
  have neighbors := neighbors_unchanged keys history active.1
  unfold External
  rw [← left_none current, ← left_none active, ← right_none current, ← right_none active,
    neighbors.1, neighbors.2]

theorem left_glancing_update {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (active : Active P q) (untouched : q.1 ∉ keys) :
    LeftGlancing (P ∪ row time keys) q ↔ LeftGlancing P q ∧ ∀ x ∈ keys, q.1 < x := by
  have fresh : q.2 < time := (history q active.1).2
  have external := external_unchanged keys history active untouched
  constructor
  · intro current
    refine ⟨⟨active, fun h => current.2.1 (external.mpr h),
      fun p hp ht => current.2.2 p (Finset.mem_union_left _ hp) ht⟩, ?_⟩
    intro x hx
    exact current.2.2 (x, time) (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩)) fresh
  · rintro ⟨old, side⟩
    refine ⟨(active_unchanged P time keys q untouched).mpr active,
      fun h => old.2.1 (external.mp h), ?_⟩
    intro p hp newer
    rcases Finset.mem_union.mp hp with hp | hp
    · exact old.2.2 p hp newer
    · exact side p.1 ((mem_row p time keys).mp hp).1

theorem right_glancing_update {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (active : Active P q) (untouched : q.1 ∉ keys) :
    RightGlancing (P ∪ row time keys) q ↔ RightGlancing P q ∧ ∀ x ∈ keys, x < q.1 := by
  have fresh : q.2 < time := (history q active.1).2
  have external := external_unchanged keys history active untouched
  constructor
  · intro current
    refine ⟨⟨active, fun h => current.2.1 (external.mpr h),
      fun p hp ht => current.2.2 p (Finset.mem_union_left _ hp) ht⟩, ?_⟩
    intro x hx
    exact current.2.2 (x, time) (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩)) fresh
  · rintro ⟨old, side⟩
    refine ⟨(active_unchanged P time keys q untouched).mpr active,
      fun h => old.2.1 (external.mp h), ?_⟩
    intro p hp newer
    rcases Finset.mem_union.mp hp with hp | hp
    · exact old.2.2 p hp newer
    · exact side p.1 ((mem_row p time keys).mp hp).1

theorem internal_unchanged {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (old : Internal P q) (untouched : q.1 ∉ keys) :
    Internal (P ∪ row time keys) q := by
  refine ⟨(active_unchanged P time keys q untouched).mpr old.1,
    fun h => old.2.1 ((external_unchanged keys history old.1 untouched).mp h), ?_⟩
  rintro (left | right)
  · exact old.2.2 (Or.inl ((left_glancing_update keys history old.1 untouched).mp left).1)
  · exact old.2.2 (Or.inr ((right_glancing_update keys history old.1 untouched).mp right).1)

end RotationBST.Geometric.GreedyASS.Items
