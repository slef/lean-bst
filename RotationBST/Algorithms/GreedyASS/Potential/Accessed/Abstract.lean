module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed.Results
open Items Reference

/-- Every new access is bounded by blue; a new red value is strictly smaller. -/
theorem new_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        WithTop.some (blue t lo searched x) ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          WithTop.some (blue t lo searched x)) :=
  top_bound t lo searches searched keys history member

/-- Lemma 3.11: an old blue access cannot gain potential. -/
theorem blue_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys)
    (old : itemColor t lo (searches ++ [searched]) P x = some .blue) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          itemValue t lo (searches ++ [searched]) P x) :=
  blue_access t lo searches searched keys history member old

/-- Lemma 3.10: resetting the old purple maximum cannot increase potential. -/
theorem purple_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n searches.length P) {x : Nat} (member : x ∈ keys)
    (old : itemColor t lo (searches ++ [searched]) P x = some .purple) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length keys) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length keys) x <
          itemValue t lo (searches ++ [searched]) P x) :=
  purple_access t lo searches searched keys history member old

/-- Lemma 3.12, including the searched key and a unit loss for new red accesses. -/
theorem red_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .red) :
    itemValue t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤
        itemValue t lo (searches ++ [searched]) P x ∧
      (itemColor t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red →
        itemValue t lo (searches ++ [searched]) (P ∪ row searches.length (greedySweep searches.length searched P)) x <
          itemValue t lo (searches ++ [searched]) P x) :=
  red_access t lo searches searched history valid member old

/-- The executable sweep puts the search strictly between an accessed item’s old row neighbors. -/
theorem search_interval {n time searched : Nat} {P : Finset Point}
    (history : History n time P) {q : Point} (active : Active P q)
    (accessed : q.1 ∈ greedySweep time searched P) {a b : Nat}
    (left : leftNeighbor P q = some a) (right : rightNeighbor P q = some b) :
    a < searched ∧ searched < b :=
  search_between history active accessed left right

/-- The natural-valued potential is exactly the finite selected potential. -/
theorem amount (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) :
    itemValue t lo searches P x = WithTop.some (itemAmount t lo searches P x) :=
  amount_exact t lo searches P x

/-- Every new red access among old red, blue, and purple items pays one unit. -/
theorem charge (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .red ∨
      itemColor t lo (searches ++ [searched]) P x = some .blue ∨
      itemColor t lo (searches ++ [searched]) P x = some .purple) :
    itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x +
      (if itemColor t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red then 1 else 0) ≤
      itemAmount t lo (searches ++ [searched]) P x :=
  unit_credit t lo searches searched history valid member old

/-- Sum the actual item potentials and pay for the resulting red accesses. -/
theorem total (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) (keys : Finset Nat)
    (accessed : keys ⊆ greedySweep searches.length searched P)
    (old : ∀ x ∈ keys, itemColor t lo (searches ++ [searched]) P x = some .red ∨
      itemColor t lo (searches ++ [searched]) P x = some .blue ∨
      itemColor t lo (searches ++ [searched]) P x = some .purple) :
    totalAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) keys +
      (coloredKeys t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) keys .red).card ≤
      totalAmount t lo (searches ++ [searched]) P keys :=
  total_credit t lo searches searched history valid keys accessed old

/-- A first access has zero old potential and at most two units of new potential. -/
theorem first_access (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P) (unseen : latest P x = none) :
    itemAmount t lo (searches ++ [searched]) P x = 0 ∧
      itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x ≤ 2 :=
  unseen_amount t lo searches searched history member unseen

/-- First-access potential and actual cost are at most three per unseen item. -/
theorem first_access_total (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (history : History n searches.length P) :
    totalAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P))
        (unseenKeys P (greedySweep searches.length searched P)) +
      (unseenKeys P (greedySweep searches.length searched P)).card ≤
      3 * (unseenKeys P (greedySweep searches.length searched P)).card :=
  unseen_total t lo searches searched history

/-- Lemma 3.9 in its amortized inequality form: an accessed green item loses at least one unit. -/
theorem green_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .green) :
    itemAmount t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x + 1 ≤
      itemAmount t lo (searches ++ [searched]) P x :=
  green_access t lo searches searched satisfied history valid member old

/-- All accessed items, including first accesses, are included. Only the new blue/purple counts and explicit startup allowance remain. -/
theorem whole_row (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) :
    let keys := greedySweep searches.length searched P
    let Q := P ∪ row searches.length keys
    keys.card + totalAmount t lo (searches ++ [searched]) Q keys ≤
      totalAmount t lo (searches ++ [searched]) P keys +
        (coloredKeys t lo (searches ++ [searched]) Q keys .blue).card +
        (coloredKeys t lo (searches ++ [searched]) Q keys .purple).card +
        3 * (unseenKeys P keys).card :=
  row_bound t lo searches searched satisfied history valid

/-- Lemma 3.9 exactly: an accessed green item becomes red and loses one unit. -/
theorem green_exact_change (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P) (history : History n searches.length P)
    (valid : ∀ q ∈ P, lo ≤ q.1 ∧ q.1 < lo + leaves t) {x : Nat}
    (member : x ∈ greedySweep searches.length searched P)
    (old : itemColor t lo (searches ++ [searched]) P x = some .green) :
    itemColor t lo (searches ++ [searched])
        (P ∪ row searches.length (greedySweep searches.length searched P)) x = some .red ∧
      itemAmount t lo (searches ++ [searched])
          (P ∪ row searches.length (greedySweep searches.length searched P)) x + 1 =
        itemAmount t lo (searches ++ [searched]) P x :=
  green_exact t lo searches searched satisfied history valid member old

end RotationBST.Geometric.GreedyASS.Potential.Accessed.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.Accessed.Results`: 13 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.Accessed.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract]
