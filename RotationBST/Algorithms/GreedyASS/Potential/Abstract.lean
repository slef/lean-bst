module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Results
open Items Reference

theorem externals (P : Finset Point) (x : Nat) :
    x ∈ externalKeys P ↔ ∃ stamp, External P (x, stamp) := mem_external P x

theorem left_neighbor (P : Finset Point) (x a : Nat) :
    leftExternal P x = some a ↔ a ∈ externalKeys P ∧ a < x ∧
      ∀ y ∈ externalKeys P, y < x → y ≤ a := left_external_spec P x a

theorem right_neighbor (P : Finset Point) (x b : Nat) :
    rightExternal P x = some b ↔ b ∈ externalKeys P ∧ x < b ∧
      ∀ y ∈ externalKeys P, x < y → b ≤ y := right_external_spec P x b

theorem red_defined (t : Tree) (lo : Nat) {P : Finset Point} {q : Point}
    (active : Active P q) (nonexternal : ¬ External P q) :
    ∃ a b, leftNeighbor P q = some a ∧ rightNeighbor P q = some b ∧
      a < q.1 ∧ q.1 < b ∧ red t lo P q = (Distance.toLCA t lo q.1 a b : Nat) :=
  red_finite t lo active nonexternal

/-- Lemma 3.14 at the retained active point of an unaccessed column. -/
theorem red_stable (t : Tree) (lo : Nat) {n time : Nat} {P : Finset Point}
    (keys : Finset Nat) (history : History n time P) {q : Point}
    (active : Active P q) (untouched : q.1 ∉ keys) :
    Active (P ∪ row time keys) q ∧ red t lo (P ∪ row time keys) q = red t lo P q :=
  ⟨(active_unchanged P time keys q untouched).mpr active, red_unchanged t lo keys history active.1⟩

theorem blue_root (t : Tree) (lo searched x : Nat) {c : Component}
    (member : c ∈ forest t lo searched) (inside : c.Contains x) :
    2 ≤ blue t lo searched x ∧ blue t lo searched x = Distance.toRoot c x + 1 :=
  ⟨blue_ge_two t lo searched x, blue_component t lo searched x member inside⟩

theorem green_infinite (t : Tree) (lo : Nat) (P : Finset Point) (x : Nat)
    (missing : leftExternal P x = none ∨ rightExternal P x = none) : green t lo P x = ⊤ :=
  green_missing t lo P x missing

/-- Candidate-value comparison; the color rule additionally handles top corners. -/
theorem green_comparison (t : Tree) (lo searched : Nat) (P : Finset Point) (x a b : Nat)
    {c : Component} (member : c ∈ forest t lo searched) (inside : c.Contains x)
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) :
    green t lo P x ≤ (blue t lo searched x : WithTop Nat) ↔ c.Contains a ∧ c.Contains b :=
  green_blue t lo searched P x a b member inside left right valid

theorem purple_update (t : Tree) (lo : Nat) (searches : List Nat) (searched stamp x : Nat)
    (old : stamp ≤ searches.length) :
    purple t lo (searches ++ [searched]) stamp x =
        max (purple t lo searches stamp x) (blue t lo searched x) ∧
      blue t lo searched x ≤ purple t lo (searches ++ [searched]) stamp x ∧
      purple t lo (searches ++ [searched]) searches.length x = blue t lo searched x :=
  ⟨purple_step t lo searches searched stamp x old, purple_ge_blue t lo searches searched stamp x old,
    purple_reset t lo searches searched x⟩

theorem internal (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (inside : Internal P q) :
    color t lo searches P q = some .red ∧ value t lo searches P q = red t lo P q :=
  internal_spec t lo searches inside

theorem glancing (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (glance : Glancing P q) :
    color t lo searches P q =
        (if red t lo P q < (purple t lo searches q.2 q.1 : WithTop Nat) then some .red else some .purple) ∧
      value t lo searches P q = min (red t lo P q) (purple t lo searches q.2 q.1 : WithTop Nat) :=
  glancing_spec t lo searches glance

theorem external (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (outside : External P q) :
    color t lo searches P q =
        (if LatestRow P q.2 then some .blue
         else if green t lo P q.1 ≤ (currentBlue t lo searches q.1 : WithTop Nat)
           then some .green else some .blue) ∧
      value t lo searches P q =
        (if LatestRow P q.2 then (currentBlue t lo searches q.1 : WithTop Nat)
         else min (green t lo P q.1) (currentBlue t lo searches q.1 : WithTop Nat)) :=
  external_spec t lo searches outside

/-- Top corners remain blue when only the reference history changes. -/
theorem corner (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (external : External P q) (latest : LatestRow P q.2) :
    color t lo searches P q = some .blue ∧
      value t lo searches P q = WithTop.some (currentBlue t lo searches q.1) :=
  corner_spec t lo searches external latest

theorem green_location (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (colored : color t lo searches P q = some .green) :
    External P q ∧ ¬ LatestRow P q.2 ∧
      green t lo P q.1 ≤ WithTop.some (currentBlue t lo searches q.1) ∧
      value t lo searches P q = green t lo P q.1 :=
  green_spec t lo searches colored

theorem finite (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) :
    ∃ v : Nat, value t lo searches P q = v := Potential.finite t lo searches P q

theorem internal_stable (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {q : Point} (inside : Internal P q) (untouched : q.1 ∉ keys) :
    value t lo searches (P ∪ row time keys) q = value t lo searches P q :=
  Potential.internal_unchanged t lo searches keys history inside untouched

theorem glancing_stable (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {q : Point} (old : Glancing P q) (new : Glancing (P ∪ row time keys) q) :
    color t lo searches (P ∪ row time keys) q = color t lo searches P q ∧
      value t lo searches (P ∪ row time keys) q = value t lo searches P q :=
  glancing_unchanged t lo searches keys history old new

theorem item (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {x stamp : Nat}
    (active : Active P (x, stamp)) :
    itemColor t lo searches P x = color t lo searches P (x, stamp) ∧
      itemValue t lo searches P x = value t lo searches P (x, stamp) :=
  item_spec t lo searches active

/-- Before adding the row, previously unseen keys have no old color. -/
theorem partition (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (keys : Finset Nat) :
    keys.card = (unseenKeys P keys).card +
      (coloredKeys t lo searches P keys .red).card + (coloredKeys t lo searches P keys .green).card +
      (coloredKeys t lo searches P keys .blue).card + (coloredKeys t lo searches P keys .purple).card :=
  Potential.partition t lo searches P keys

theorem row (t : Tree) (lo : Nat) (searches : List Nat) {n time : Nat}
    {P : Finset Point} (keys : Finset Nat) (history : History n time P) :
    keys.card =
      (coloredKeys t lo searches (P ∪ row time keys) keys .red).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .green).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .blue).card +
      (coloredKeys t lo searches (P ∪ row time keys) keys .purple).card :=
  row_partition t lo searches keys history

theorem first_accesses (time : Nat) (P : Finset Point) (xs : List Nat) :
    (P.image Prod.fst).card + firstAccesses time P xs =
      ((fill greedySweep time P xs).image Prod.fst).card := first_access_exact time P xs

/-- Unseen keys in intermediate row partitions require only a one-time
universe-size allowance along the actual executable sweep. -/
theorem startup {n time : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n time P) (satisfied : ASS P) (valid : ∀ x ∈ xs, x < n) :
    (P.image Prod.fst).card + firstAccesses time P xs ≤ n :=
  first_access_bound xs history satisfied valid

end RotationBST.Geometric.GreedyASS.Potential.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.Results`: 22 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract]
