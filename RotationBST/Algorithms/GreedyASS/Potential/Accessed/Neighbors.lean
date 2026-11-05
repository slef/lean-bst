module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Accounting
public import RotationBST.Algorithms.GreedyASS.Items.External
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Accessed
open Items Reference

/-- Both nearest external neighbors of a non-corner left-external item
belong to the same exposed chain. -/
theorem left_neighbors {P : Finset Point} (satisfied : ASS P) {q : Point}
    (external : LeftExternal P q) (notTop : ¬ LatestRow P q.2) {a b : Nat}
    (left : leftExternal P q.1 = some a) (right : rightExternal P q.1 = some b) :
    ∃ ta tb, LeftExternal P (a, ta) ∧ LeftExternal P (b, tb) := by
  have ha := (left_external_spec P q.1 a).mp left
  have hb := (right_external_spec P q.1 b).mp right
  obtain ⟨ta, ea⟩ := (mem_external P a).mp ha.1
  obtain ⟨tb, eb⟩ := (mem_external P b).mp hb.1
  obtain ⟨p, r, ep, _, latest, _⟩ := latest_corners ⟨q, external.1.1⟩
  have qp := left_before_corner satisfied external notTop ep.1.1 latest
  have pkey : p.1 ∈ externalKeys P := (mem_external P p.1).mpr ⟨p.2, Or.inl ep⟩
  have bp := hb.2.2 p.1 pkey qp
  refine ⟨ta, tb, ?_, ?_⟩
  · rcases ea with ea | ea
    · exact ea
    · have order := external_order satisfied external ea
      have ax := ha.2.1
      simp only at order
      omega
  · rcases eb with eb | eb
    · exact eb
    · have order := external_order satisfied ep eb
      have same : b = p.1 := by simp only at order; omega
      have equal := active_unique ep.1 eb.1 same
      simpa only [equal] using ep

theorem right_neighbors {P : Finset Point} (satisfied : ASS P) {q : Point}
    (external : RightExternal P q) (notTop : ¬ LatestRow P q.2) {a b : Nat}
    (left : leftExternal P q.1 = some a) (right : rightExternal P q.1 = some b) :
    ∃ ta tb, RightExternal P (a, ta) ∧ RightExternal P (b, tb) := by
  have ha := (left_external_spec P q.1 a).mp left
  have hb := (right_external_spec P q.1 b).mp right
  obtain ⟨ta, ea⟩ := (mem_external P a).mp ha.1
  obtain ⟨tb, eb⟩ := (mem_external P b).mp hb.1
  obtain ⟨p, r, _, er, latest, sameTime⟩ := latest_corners ⟨q, external.1.1⟩
  have latestR : LatestRow P r.2 := by simpa only [sameTime] using latest
  have rq := right_after_corner satisfied external notTop er.1.1 latestR
  have rkey : r.1 ∈ externalKeys P := (mem_external P r.1).mpr ⟨r.2, Or.inr er⟩
  have ra := ha.2.2 r.1 rkey rq
  refine ⟨ta, tb, ?_, ?_⟩
  · rcases ea with ea | ea
    · have order := external_order satisfied ea er
      have same : a = r.1 := by simp only at order; omega
      have equal := active_unique er.1 ea.1 same
      simpa only [equal] using er
    · exact ea
  · rcases eb with eb | eb
    · have order := external_order satisfied eb external
      have xb := hb.2.1
      simp only at order
      omega
    · exact eb

theorem left_access {P : Finset Point} (satisfied : ASS P) {q : Point}
    (external : LeftExternal P q) (time searched : Nat) (old : q.2 ≤ time)
    (side : searched ≤ q.1) : q.1 ∈ greedySweep time searched P := by
  by_cases same : q.1 = searched
  · simp [greedySweep, same]
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨external.1.1, same, ?_⟩, rfl⟩
    intro p hp different rectangle
    have horizontal : p.1 ≤ q.1 := by
      simpa only [max_eq_left side] using rectangle.2.1
    have vertical : q.2 ≤ p.2 := by
      simpa only [min_eq_left old] using rectangle.2.2.1
    exact different (left_quadrant satisfied external hp horizontal vertical)

theorem right_access {P : Finset Point} (satisfied : ASS P) {q : Point}
    (external : RightExternal P q) (time searched : Nat) (old : q.2 ≤ time)
    (side : q.1 ≤ searched) : q.1 ∈ greedySweep time searched P := by
  by_cases same : q.1 = searched
  · simp [greedySweep, same]
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    refine ⟨q, Finset.mem_filter.mpr ⟨external.1.1, same, ?_⟩, rfl⟩
    intro p hp different rectangle
    have horizontal : q.1 ≤ p.1 := by
      simpa only [min_eq_left side] using rectangle.1
    have vertical : q.2 ≤ p.2 := by
      simpa only [min_eq_left old] using rectangle.2.2.1
    exact different (right_quadrant satisfied external hp horizontal vertical)

/-- Two points on the left-external chain appear in increasing time order. -/
theorem left_time {P : Finset Point} (satisfied : ASS P) {q r : Point}
    (qactive : Active P q) (external : LeftExternal P r) (qr : q.1 < r.1) : q.2 < r.2 := by
  by_contra time
  have same := left_quadrant satisfied external qactive.1 qr.le (by omega)
  have coord := congrArg Prod.fst same
  omega

theorem right_time {P : Finset Point} (satisfied : ASS P) {p q : Point}
    (qactive : Active P q) (external : RightExternal P p) (pq : p.1 < q.1) : q.2 < p.2 := by
  by_contra time
  have same := right_quadrant satisfied external qactive.1 pq.le (by omega)
  have coord := congrArg Prod.fst same
  omega

/-- On either exposed chain, an accessed non-corner item whose search is
outside its external-neighbor interval brings both neighbors into the row. -/
theorem external_access_bracket {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {q : Point}
    (external : External P q) (notTop : ¬ LatestRow P q.2)
    (accessed : q.1 ∈ greedySweep time searched P) {a b : Nat}
    (left : leftExternal P q.1 = some a) (right : rightExternal P q.1 = some b)
    (outside : searched < a ∨ b < searched) :
    a ∈ greedySweep time searched P ∧ b ∈ greedySweep time searched P ∧
      ((searched < a ∧ ∃ ta, LeftExternal P (a, ta)) ∨
        (b < searched ∧ ∃ tb, RightExternal P (b, tb))) := by
  have ha := (left_external_spec P q.1 a).mp left
  have hb := (right_external_spec P q.1 b).mp right
  rcases external with external | external
  · obtain ⟨ta, tb, ea, eb⟩ := left_neighbors satisfied external notTop left right
    have side : searched < a := by
      rcases outside with side | side
      · exact side
      · have different : q.1 ≠ searched := by have := hb.2.1; omega
        have visible := access_visible history external.1 accessed different
        have later := left_time satisfied external.1 eb hb.2.1
        have age := (history (b, tb) eb.1.1).2
        exfalso
        apply visible.2 (b, tb) eb.1.1
          (by intro eq; have := congrArg Prod.fst eq; simp only at this; have := hb.2.1; omega)
        simp only [Rectangle]
        have order := hb.2.1
        exact ⟨(min_le_left _ _).trans order.le, side.le.trans (le_max_right _ _),
          (min_le_left _ _).trans later.le, age.le.trans (le_max_right _ _)⟩
    exact ⟨left_access satisfied ea time searched (history _ ea.1.1).2.le side.le,
      left_access satisfied eb time searched (history _ eb.1.1).2.le (by have := ha.2.1; have := hb.2.1; omega),
      Or.inl ⟨side, ta, ea⟩⟩
  · obtain ⟨ta, tb, ea, eb⟩ := right_neighbors satisfied external notTop left right
    have side : b < searched := by
      rcases outside with side | side
      · have different : q.1 ≠ searched := by have := ha.2.1; omega
        have visible := access_visible history external.1 accessed different
        have later := right_time satisfied external.1 ea ha.2.1
        have age := (history (a, ta) ea.1.1).2
        exfalso
        apply visible.2 (a, ta) ea.1.1
          (by intro eq; have := congrArg Prod.fst eq; simp only at this; have := ha.2.1; omega)
        simp only [Rectangle]
        have order := ha.2.1
        exact ⟨(min_le_right _ _).trans side.le, order.le.trans (le_max_left _ _),
          (min_le_left _ _).trans later.le, age.le.trans (le_max_right _ _)⟩
      · exact side
    exact ⟨right_access satisfied ea time searched (history _ ea.1.1).2.le (by have := ha.2.1; have := hb.2.1; omega),
      right_access satisfied eb time searched (history _ eb.1.1).2.le side.le, Or.inr ⟨side, tb, eb⟩⟩

end RotationBST.Geometric.GreedyASS.Potential.Accessed
