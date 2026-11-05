module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.Unaccessed.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results
open Items Reference

/-- Every new access lies on one side of an untouched external item. -/
theorem sweep_side {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {q : Point}
    (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    (∀ y ∈ greedySweep time searched P, y < q.1) ∨
      (∀ y ∈ greedySweep time searched P, q.1 < y) :=
  one_side satisfied history external untouched

/-- External neighbors can only move inward when the new row lies on one side. -/
theorem neighbor_interval {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x a b : Nat}
    (left : leftExternal P x = some a) (right : rightExternal P x = some b)
    (side : (∀ y ∈ keys, y < x) ∨ (∀ y ∈ keys, x < y)) :
    ∃ u v, leftExternal (P ∪ row time keys) x = some u ∧
      rightExternal (P ∪ row time keys) x = some v ∧ a ≤ u ∧ u < x ∧ x < v ∧ v ≤ b :=
  neighbors_nested keys history left right side

/-- The green candidate cannot increase under a one-sided later row. -/
theorem green_change (t : Tree) (lo : Nat) {n time : Nat} {P : Finset Point}
    (keys : Finset Nat) (history : History n time P) (x : Nat)
    (side : (∀ y ∈ keys, y < x) ∨ (∀ y ∈ keys, x < y)) :
    green t lo (P ∪ row time keys) x ≤ green t lo P x :=
  green_mono t lo keys history x side

/-- Lemma 3.13, including old top corners: an untouched external point cannot gain potential. -/
theorem external_point (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    {q : Point} (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    value t lo searches (P ∪ row time (greedySweep time searched P)) q ≤
      value t lo searches P q :=
  external_value t lo searches satisfied history external untouched

/-- Lemma 3.13 for the natural-valued latest-item query. -/
theorem external_change (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    {q : Point} (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    itemAmount t lo searches (P ∪ row time (greedySweep time searched P)) q.1 ≤
      itemAmount t lo searches P q.1 :=
  external_amount t lo searches satisfied history external untouched

/-- Sum the external-item nonincrease over any untouched subset. -/
theorem external_sum (t : Tree) (lo : Nat) (searches : List Nat)
    {n time searched : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n time P)
    (keys : Finset Nat) (external : keys ⊆ externalKeys P)
    (untouched : ∀ x ∈ keys, x ∉ greedySweep time searched P) :
    totalAmount t lo searches (P ∪ row time (greedySweep time searched P)) keys ≤
      totalAmount t lo searches P keys :=
  external_total t lo searches satisfied history keys external untouched

/-- An untouched red item keeps its color and amount, including glancing-to-internal changes. -/
theorem red_unchanged (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {x : Nat} (colored : itemColor t lo searches P x = some .red) (untouched : x ∉ keys) :
    itemColor t lo searches (P ∪ row time keys) x = some .red ∧
      itemAmount t lo searches (P ∪ row time keys) x = itemAmount t lo searches P x :=
  red_amount t lo searches keys history colored untouched


/-- Historical purple covers red for every internal point of an actual greedy history; this supplies Lemma 3.16. -/
theorem internal_cover (t : Tree) (lo : Nat) (searches : List Nat) {n : Nat}
    (valid : ∀ y ∈ searches, y < n) {q : Point} (internal : Internal (Virgin.points searches) q) :
    red t lo (Virgin.points searches) q ≤ WithTop.some (purple t lo searches q.2 q.1) :=
  internal_purple t lo searches valid internal

/-- Lemma 3.17, including glancing-to-internal changes. -/
theorem nonexternal_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) {q : Point}
    (active : Active (Virgin.points searches) q) (nonexternal : ¬ External (Virgin.points searches) q)
    (untouched : q.1 ∉ Virgin.keys searches searched) :
    value t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) q ≤
      value t lo (searches ++ [searched]) (Virgin.points searches) q :=
  nonexternal_value t lo searches searched valid active nonexternal untouched

/-- Every untouched item has nonincreasing natural-valued potential, including unseen columns. -/
theorem untouched_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) {x : Nat}
    (untouched : x ∉ Virgin.keys searches searched) :
    itemAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) x ≤
      itemAmount t lo (searches ++ [searched]) (Virgin.points searches) x :=
  all_amount t lo searches searched valid untouched

/-- Sum the complete unaccessed contribution to Phase II. -/
theorem untouched_sum (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat) {n : Nat}
    (valid : ∀ y ∈ searches ++ [searched], y < n) (keys : Finset Nat)
    (untouched : ∀ x ∈ keys, x ∉ Virgin.keys searches searched) :
    totalAmount t lo (searches ++ [searched]) (Virgin.points (searches ++ [searched])) keys ≤
      totalAmount t lo (searches ++ [searched]) (Virgin.points searches) keys :=
  all_total t lo searches searched valid keys untouched

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results`: 11 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.Unaccessed.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Virgin.Definitions.Abstract]
