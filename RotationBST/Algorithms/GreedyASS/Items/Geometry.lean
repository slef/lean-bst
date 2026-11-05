module

public import RotationBST.Algorithms.GreedyASS.Items.Neighbors
public import RotationBST.Models.Geometric.Rectangle
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

theorem active_unique {P : Finset Point} {q p : Point}
    (hq : Active P q) (hp : Active P p) (column : p.1 = q.1) : p = q := by
  have first := hq.2 p hp.1 column
  have second := hp.2 q hq.1 column.symm
  exact Prod.ext column (by omega)

/-- In an ASS, a left-external active point is the only point in its closed
upper-left quadrant. This uses satisfaction, not just the same-row test. -/
theorem left_quadrant {P : Finset Point} {q : Point} (satisfied : ASS P)
    (external : LeftExternal P q) {p : Point} (member : p ∈ P)
    (left : p.1 ≤ q.1) (above : q.2 ≤ p.2) : p = q := by
  by_cases column : p.1 = q.1
  · have upper := external.1.2 p member column
    exact Prod.ext column (by omega)
  by_cases sameRow : p.2 = q.2
  · have lower := external.2 p member sameRow
    exact (column (by omega)).elim
  obtain ⟨w, hw, different, _, rectangle, side⟩ := side_witness satisfied
    external.1.1 member (Ne.symm column) (Ne.symm sameRow)
  unfold Rectangle at rectangle
  exfalso
  apply different
  rcases side with col | rw
  · have upper := external.1.2 w hw col
    exact Prod.ext col (by omega)
  · have lower := external.2 w hw rw
    exact Prod.ext (by omega) rw

theorem right_quadrant {P : Finset Point} {q : Point} (satisfied : ASS P)
    (external : RightExternal P q) {p : Point} (member : p ∈ P)
    (right : q.1 ≤ p.1) (above : q.2 ≤ p.2) : p = q := by
  by_cases column : p.1 = q.1
  · have upper := external.1.2 p member column
    exact Prod.ext column (by omega)
  by_cases sameRow : p.2 = q.2
  · have upper := external.2 p member sameRow
    exact (column (by omega)).elim
  obtain ⟨w, hw, different, _, rectangle, side⟩ := side_witness satisfied
    external.1.1 member (Ne.symm column) (Ne.symm sameRow)
  unfold Rectangle at rectangle
  exfalso
  apply different
  rcases side with col | rw
  · have upper := external.1.2 w hw col
    exact Prod.ext col (by omega)
  · have upper := external.2 w hw rw
    exact Prod.ext (by omega) rw

/-- A left-external point farther right witnesses that an active point
cannot be on the latest row of the snapshot. -/
theorem left_not_latest {P : Finset Point} (satisfied : ASS P) {q r : Point}
    (active : Active P q) (right : LeftExternal P r) (qr : q.1 < r.1) :
    ¬ LatestRow P q.2 := by
  intro latest
  have same := left_quadrant satisfied right active.1 qr.le (latest r right.1.1)
  have coord := congrArg Prod.fst same
  omega

theorem right_not_latest {P : Finset Point} (satisfied : ASS P) {p q : Point}
    (active : Active P q) (left : RightExternal P p) (pq : p.1 < q.1) :
    ¬ LatestRow P q.2 := by
  intro latest
  have same := right_quadrant satisfied left active.1 pq.le (latest p left.1.1)
  have coord := congrArg Prod.fst same
  omega

/-- Externality is equivalent to the corresponding exposed quadrant once
arboral satisfaction and activity are known. -/
theorem left_external_iff {P : Finset Point} {q : Point} (satisfied : ASS P)
    (active : Active P q) :
    LeftExternal P q ↔ ∀ p ∈ P, p.1 ≤ q.1 → q.2 ≤ p.2 → p = q := by
  constructor
  · exact fun external p hp hl ht => left_quadrant satisfied external hp hl ht
  · intro exposed
    refine ⟨active, ?_⟩
    intro p hp row
    by_contra left
    have eq := exposed p hp (by omega) (by omega)
    have := congrArg Prod.fst eq
    omega

theorem right_external_iff {P : Finset Point} {q : Point} (satisfied : ASS P)
    (active : Active P q) :
    RightExternal P q ↔ ∀ p ∈ P, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q := by
  constructor
  · exact fun external p hp hr ht => right_quadrant satisfied external hp hr ht
  · intro exposed
    refine ⟨active, ?_⟩
    intro p hp row
    by_contra right
    have eq := exposed p hp (by omega) (by omega)
    have := congrArg Prod.fst eq
    omega

/-- The three location classes partition the active points. -/
theorem classification {P : Finset Point} {q : Point} (active : Active P q) :
    (External P q ∨ Glancing P q ∨ Internal P q) ∧
      ¬ (External P q ∧ Glancing P q) ∧
      ¬ (External P q ∧ Internal P q) ∧ ¬ (Glancing P q ∧ Internal P q) := by
  have noExternal : Glancing P q → ¬ External P q := by
    rintro (h | h) <;> exact h.2.1
  constructor
  · by_cases external : External P q
    · exact Or.inl external
    · by_cases glancing : Glancing P q
      · exact Or.inr (Or.inl glancing)
      · exact Or.inr (Or.inr ⟨active, external, glancing⟩)
  · exact ⟨fun h => noExternal h.2 h.1, fun h => h.2.2.1 h.1, fun h => h.2.2.2 h.1⟩

end RotationBST.Geometric.GreedyASS.Items
