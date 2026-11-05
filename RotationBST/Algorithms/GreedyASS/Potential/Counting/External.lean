module

public import RotationBST.Algorithms.GreedyASS.Potential.Counting.Purple
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Counting
open Items Reference

/-- Among three external items in one component, an old middle item is
green. The newest-row exclusion is geometric, so it also applies during
Phase I when the search history is ahead of the point set. -/
theorem middle_green (t : Tree) (lo : Nat) (searches : List Nat) (searched : Nat)
    {P : Finset Point} {c : Component} (component : c ∈ forest t lo searched) {p q r : Point}
    (left : External P p) (middle : External P q) (right : External P r)
    (insideP : c.Contains p.1) (insideQ : c.Contains q.1) (insideR : c.Contains r.1)
    (pq : p.1 < q.1) (qr : q.1 < r.1) (notTop : ¬ LatestRow P q.2) :
    color t lo (searches ++ [searched]) P q = some .green := by
  obtain ⟨a, b, ha, hb, pa, aq, qb, br⟩ := external_bracket left right pq qr
  have nested := Distance.enclosing t lo q.1 p.1 a b r.1 pa (by omega) br
  have bounds := Reference.bounds t lo searched component
  have validP : lo ≤ p.1 ∧ p.1 < lo + leaves t := by
    unfold Component.Contains at insideP
    omega
  have validR : lo ≤ r.1 ∧ r.1 < lo + leaves t := by
    unfold Component.Contains at insideR
    omega
  have rootBound := (Distance.forest_compare t lo searched p.1 q.1 r.1 component insideQ
    pq.le qr.le validP validR).mpr ⟨insideP, insideR⟩
  have blueRoot := blue_component t lo searched q.1 component insideQ
  have current : currentBlue t lo (searches ++ [searched]) q.1 = blue t lo searched q.1 := by
    simp [currentBlue]
  have below : green t lo P q.1 ≤ WithTop.some (currentBlue t lo (searches ++ [searched]) q.1) := by
    have numeric : Distance.toLCA t lo q.1 a b + 1 ≤ blue t lo searched q.1 := by omega
    simpa only [green, ha, hb, current, WithTop.coe_le_coe] using numeric
  simpa only [notTop, ↓reduceIte, below] using (external_spec t lo (searches ++ [searched]) middle).1

/-- A left-external item with a left-external item farther right cannot be
a top corner: that newer corner would lie in the other's exposed quadrant. -/
theorem left_old {n time : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (time + 1) P) {q r : Point} (active : Active P q)
    (right : LeftExternal P r) (qr : q.1 < r.1) : q.2 < time := by
  have qtime := (history q active.1).2
  have rtime := (history r right.1.1).2
  by_contra newer
  have same := left_quadrant satisfied right active.1 qr.le (by omega)
  have coord := congrArg Prod.fst same
  omega

theorem right_old {n time : Nat} {P : Finset Point} (satisfied : ASS P)
    (history : History n (time + 1) P) {p q : Point} (active : Active P q)
    (left : RightExternal P p) (pq : p.1 < q.1) : q.2 < time := by
  have qtime := (history q active.1).2
  have ptime := (history p left.1.1).2
  by_contra newer
  have same := right_quadrant satisfied left active.1 pq.le (by omega)
  have coord := congrArg Prod.fst same
  omega

end RotationBST.Geometric.GreedyASS.Potential.Counting
