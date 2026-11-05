module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Items.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items.Results

theorem most_recent (P : Finset Point) (key stamp : Nat) :
    latest P key = some stamp ↔ Active P (key, stamp) := latest_spec P key stamp

theorem left_neighbor (P : Finset Point) (q : Point) (key : Nat) :
    leftNeighbor P q = some key ↔
      (key, q.2) ∈ P ∧ key < q.1 ∧ ∀ x, (x, q.2) ∈ P → x < q.1 → x ≤ key :=
  left_spec P q key

theorem right_neighbor (P : Finset Point) (q : Point) (key : Nat) :
    rightNeighbor P q = some key ↔
      (key, q.2) ∈ P ∧ q.1 < key ∧ ∀ x, (x, q.2) ∈ P → q.1 < x → key ≤ x :=
  right_spec P q key

theorem missing_neighbors {P : Finset Point} {q : Point} (active : Active P q) :
    (leftNeighbor P q = none ↔ LeftExternal P q) ∧
      (rightNeighbor P q = none ↔ RightExternal P q) := ⟨left_none active, right_none active⟩

theorem neighbors {P : Finset Point} {q : Point} (active : Active P q)
    (notExternal : ¬ External P q) :
    ∃ l r, leftNeighbor P q = some l ∧ rightNeighbor P q = some r :=
  neighbors_exist active notExternal

/-- External points are precisely the exposed upper quadrant corners in an ASS. -/
theorem quadrants {P : Finset Point} {q : Point} (satisfied : ASS P) (active : Active P q) :
    (LeftExternal P q ↔ ∀ p ∈ P, p.1 ≤ q.1 → q.2 ≤ p.2 → p = q) ∧
      (RightExternal P q ↔ ∀ p ∈ P, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q) :=
  ⟨left_external_iff satisfied active, right_external_iff satisfied active⟩

theorem classes {P : Finset Point} {q : Point} (active : Active P q) :
    (External P q ∨ Glancing P q ∨ Internal P q) ∧
      ¬ (External P q ∧ Glancing P q) ∧
      ¬ (External P q ∧ Internal P q) ∧ ¬ (Glancing P q ∧ Internal P q) := classification active

/-- Fact 3.3 and the corresponding latest-access and externality invariants. -/
theorem unchanged {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (active : Active P q) (untouched : q.1 ∉ keys) :
    latest (P ∪ row time keys) q.1 = latest P q.1 ∧ Active (P ∪ row time keys) q ∧
      leftNeighbor (P ∪ row time keys) q = leftNeighbor P q ∧
      rightNeighbor (P ∪ row time keys) q = rightNeighbor P q ∧
      (External (P ∪ row time keys) q ↔ External P q) :=
  ⟨latest_unchanged P time keys q.1 untouched,
    (active_unchanged P time keys q untouched).mpr active,
    (neighbors_unchanged keys history active.1).1, (neighbors_unchanged keys history active.1).2,
    external_unchanged keys history active untouched⟩

theorem glancing_update {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (active : Active P q) (untouched : q.1 ∉ keys) :
    (LeftGlancing (P ∪ row time keys) q ↔ LeftGlancing P q ∧ ∀ x ∈ keys, q.1 < x) ∧
      (RightGlancing (P ∪ row time keys) q ↔ RightGlancing P q ∧ ∀ x ∈ keys, x < q.1) :=
  ⟨left_glancing_update keys history active untouched, right_glancing_update keys history active untouched⟩

theorem internal {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {q : Point} (old : Internal P q) (untouched : q.1 ∉ keys) :
    Internal (P ∪ row time keys) q := internal_unchanged keys history old untouched

/-- Every new access is external or glancing, never internal. -/
theorem accessed {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys) :
    (External (P ∪ row time keys) (x, time) ∨ Glancing (P ∪ row time keys) (x, time)) ∧
      ¬ Internal (P ∪ row time keys) (x, time) := top_classification keys history member

theorem top_corners {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) : (corners P time keys).card ≤ 2 := corners_bound keys history

/-- The latest row belongs to the point-set snapshot, not a separate
search-history clock. On a completed nonempty row the tests agree. -/
theorem latest_row {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) (nonempty : keys.Nonempty) {q : Point}
    (member : q ∈ P ∪ row time keys) : LatestRow (P ∪ row time keys) q.2 ↔ q.2 = time :=
  latest_row_iff keys history nonempty member

theorem noncorner {P : Finset Point} (satisfied : ASS P) {p q r : Point}
    (active : Active P q) :
    (LeftExternal P r → q.1 < r.1 → ¬ LatestRow P q.2) ∧
      (RightExternal P p → p.1 < q.1 → ¬ LatestRow P q.2) :=
  ⟨left_not_latest satisfied active, right_not_latest satisfied active⟩

/-- The two external chains are ordered and cannot cross. -/
theorem external_chains {P : Finset Point} (satisfied : ASS P) {p q : Point}
    (left : LeftExternal P p) (right : RightExternal P q) : p.1 ≤ q.1 :=
  external_order satisfied left right

/-- Both corners exist on the actual latest row of every nonempty snapshot. -/
theorem latest_corners {P : Finset Point} (nonempty : P.Nonempty) :
    ∃ p q, LeftExternal P p ∧ RightExternal P q ∧ LatestRow P p.2 ∧ q.2 = p.2 :=
  Items.latest_corners nonempty

end RotationBST.Geometric.GreedyASS.Items.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Items.Results`: 16 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Items.Results allowing [
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract]
