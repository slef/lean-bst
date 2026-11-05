module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.GreedyASS.Potential.Counting.AbstractBridge

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting.Results
open Items Reference

theorem glancing_neighbors {P : Finset Point} (satisfied : ASS P) {p q r : Point}
    (left : Glancing P p) (middle : Glancing P q) (right : Glancing P r)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    ∃ a b, leftNeighbor P q = some a ∧ rightNeighbor P q = some b ∧
      p.1 ≤ a ∧ a < q.1 ∧ q.1 < b ∧ b ≤ r.1 := bracket satisfied left middle right pq qr

theorem red_middle (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) {p q r : Point}
    (left : Glancing P p) (middle : Glancing P q) (right : Glancing P r)
    (insideP : c.Contains p.1) (insideQ : c.Contains q.1) (insideR : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    color t lo (searches ++ [searched]) P q = some .red :=
  middle_red t lo searches searched satisfied history component left middle right insideP insideQ insideR pq qr

theorem external_neighbors {P : Finset Point} {p q r : Point}
    (left : External P p) (right : External P r) (pq : p.1 < q.1) (qr : q.1 < r.1) :
    ∃ a b, leftExternal P q.1 = some a ∧ rightExternal P q.1 = some b ∧
      p.1 ≤ a ∧ a < q.1 ∧ q.1 < b ∧ b ≤ r.1 := external_bracket left right pq qr

theorem green_middle (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {P : Finset Point} {c : Component} (component : c ∈ forest t lo searched) {p q r : Point}
    (left : External P p) (middle : External P q) (right : External P r)
    (insideP : c.Contains p.1) (insideQ : c.Contains q.1) (insideR : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) (notTop : ¬ LatestRow P q.2) :
    color t lo (searches ++ [searched]) P q = some .green :=
  middle_green t lo searches searched component left middle right insideP insideQ insideR pq qr notTop

theorem locations (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (x : Nat) :
    (itemColor t lo searches P x = some .purple →
      ∃ stamp, Active P (x, stamp) ∧ Glancing P (x, stamp) ∧
        color t lo searches P (x, stamp) = some .purple) ∧
    (itemColor t lo searches P x = some .blue →
      ∃ stamp, Active P (x, stamp) ∧ External P (x, stamp) ∧
        color t lo searches P (x, stamp) = some .blue) :=
  ⟨purple_point t lo searches P x, blue_point t lo searches P x⟩

theorem directional (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (leftBlueKeys t lo (searches ++ [searched]) P c).card ≤ 2 ∧
      (rightBlueKeys t lo (searches ++ [searched]) P c).card ≤ 2 :=
  ⟨left_blue_count t lo searches searched satisfied history component,
    right_blue_count t lo searches searched satisfied history component⟩

/-- Lemma 3.1, including top corners and the actual historical purple values. -/
theorem counts (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (searches.length + 1) P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (blueKeys t lo (searches ++ [searched]) P c).card ≤ 4 ∧
      (purpleKeys t lo (searches ++ [searched]) P c).card ≤ 2 :=
  ⟨blue_count t lo searches searched satisfied history component,
    purple_count t lo searches searched satisfied history component⟩

/-- The same bounds hold after changing forests but before adding the row. -/
theorem intermediate (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {n : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n searches.length P) {c : Component}
    (component : c ∈ forest t lo searched) :
    (blueKeys t lo (searches ++ [searched]) P c).card ≤ 4 ∧
      (purpleKeys t lo (searches ++ [searched]) P c).card ≤ 2 :=
  counts t lo searches searched satisfied
    (fun p hp => ⟨(history p hp).1, Nat.lt_succ_of_lt (history p hp).2⟩) component

end RotationBST.Geometric.GreedyASS.Potential.Counting.Results

/-- info: abstract audit passed for `RotationBST.Geometric.GreedyASS.Potential.Counting.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.GreedyASS.Potential.Counting.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Geometric.Definitions.Abstract,
  RotationBST.Models.Geometric.Online.Abstract,
  RotationBST.Models.Geometric.Offline.Abstract,
  RotationBST.Algorithms.GreedyASS.Algorithm.Abstract,
  RotationBST.Algorithms.GreedyASS.Items.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Reference.Distance.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Definitions.Abstract,
  RotationBST.Algorithms.GreedyASS.Potential.Counting.Definitions.Abstract]
