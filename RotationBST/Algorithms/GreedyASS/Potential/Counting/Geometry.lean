module

public import RotationBST.Algorithms.GreedyASS.Items.Geometry
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting
open Items

/-- A glancing point to the left prevents the middle active point's nearest
left neighbor from lying farther left. All relative access times are allowed. -/
theorem left_bracket {P : Finset Point} (satisfied : ASS P) {p q : Point} {a : Nat}
    (outer : Glancing P p) (active : Active P q) (left : p.1 < q.1)
    (neighbor : leftNeighbor P q = some a) : p.1 ≤ a := by
  have outerActive : Active P p := outer.elim (fun h => h.1) (fun h => h.1)
  obtain ⟨member, before, nearest⟩ := (left_spec P q a).mp neighbor
  rcases lt_trichotomy p.2 q.2 with older | same | newer
  · rcases outer with glancing | glancing
    · have := glancing.2.2 (a, q.2) member older
      omega
    · have := glancing.2.2 q active.1 older
      omega
  · have onRow : (p.1, q.2) ∈ P := by simpa only [← same, Prod.eta] using outerActive.1
    exact nearest p.1 onRow left
  · obtain ⟨w, hw, different, _, rectangle, side⟩ :=
      side_witness satisfied active.1 outerActive.1 (by omega) (by omega)
    unfold Rectangle at rectangle
    rcases side with column | sameRow
    · have upper := active.2 w hw column
      have eq : w = q := Prod.ext column (by omega)
      exact (different eq).elim
    · have unequal : w.1 ≠ q.1 := fun equal => different (Prod.ext equal sameRow)
      have onRow : (w.1, q.2) ∈ P := by simpa only [← sameRow, Prod.eta] using hw
      have bound := nearest w.1 onRow (by omega)
      omega

theorem right_bracket {P : Finset Point} (satisfied : ASS P) {q p : Point} {b : Nat}
    (outer : Glancing P p) (active : Active P q) (right : q.1 < p.1)
    (neighbor : rightNeighbor P q = some b) : b ≤ p.1 := by
  have outerActive : Active P p := outer.elim (fun h => h.1) (fun h => h.1)
  obtain ⟨member, after, nearest⟩ := (right_spec P q b).mp neighbor
  rcases lt_trichotomy p.2 q.2 with older | same | newer
  · rcases outer with glancing | glancing
    · have := glancing.2.2 q active.1 older
      omega
    · have := glancing.2.2 (b, q.2) member older
      omega
  · have onRow : (p.1, q.2) ∈ P := by simpa only [← same, Prod.eta] using outerActive.1
    exact nearest p.1 onRow right
  · obtain ⟨w, hw, different, _, rectangle, side⟩ :=
      side_witness satisfied active.1 outerActive.1 (by omega) (by omega)
    unfold Rectangle at rectangle
    rcases side with column | sameRow
    · have upper := active.2 w hw column
      have eq : w = q := Prod.ext column (by omega)
      exact (different eq).elim
    · have unequal : w.1 ≠ q.1 := fun equal => different (Prod.ext equal sameRow)
      have onRow : (w.1, q.2) ∈ P := by simpa only [← sameRow, Prod.eta] using hw
      have bound := nearest w.1 onRow (by omega)
      omega

/-- Same-row neighbors of the middle glancing item lie between the outer
glancing items, even when their most recent accesses have different times. -/
theorem bracket {P : Finset Point} (satisfied : ASS P) {p q r : Point}
    (left : Glancing P p) (middle : Glancing P q) (right : Glancing P r)
    (pq : p.1 < q.1) (qr : q.1 < r.1) :
    ∃ a b, leftNeighbor P q = some a ∧ rightNeighbor P q = some b ∧
      p.1 ≤ a ∧ a < q.1 ∧ q.1 < b ∧ b ≤ r.1 := by
  have active : Active P q := middle.elim (fun h => h.1) (fun h => h.1)
  have nonexternal : ¬ External P q := middle.elim (fun h => h.2.1) (fun h => h.2.1)
  obtain ⟨a, b, ha, hb⟩ := neighbors_exist active nonexternal
  exact ⟨a, b, ha, hb, left_bracket satisfied left active pq ha,
    ((left_spec P q a).mp ha).2.1, ((right_spec P q b).mp hb).2.1,
    right_bracket satisfied right active qr hb⟩

end RotationBST.Geometric.GreedyASS.Potential.Counting
