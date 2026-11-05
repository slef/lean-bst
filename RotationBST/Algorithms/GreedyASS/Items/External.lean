module

public import RotationBST.Algorithms.GreedyASS.Items.TopRow
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

/-- Left-external and right-external chains cannot cross. -/
theorem external_order {P : Finset Point} (satisfied : ASS P) {p q : Point}
    (left : LeftExternal P p) (right : RightExternal P q) : p.1 ≤ q.1 := by
  by_contra crossed
  have qp : q.1 < p.1 := Nat.lt_of_not_ge crossed
  by_cases time : p.2 ≤ q.2
  · have same := left_quadrant satisfied left right.1.1 qp.le time
    have coord := congrArg Prod.fst same
    omega
  · have same := right_quadrant satisfied right left.1.1 qp.le (by omega)
    have coord := congrArg Prod.fst same
    omega

/-- A nonempty snapshot has a left and right corner on its actual latest
row. This construction does not use a request-history clock. -/
theorem latest_corners {P : Finset Point} (nonempty : P.Nonempty) :
    ∃ p q, LeftExternal P p ∧ RightExternal P q ∧ LatestRow P p.2 ∧ q.2 = p.2 := by
  have timesNonempty : (P.image Prod.snd).Nonempty := nonempty.image Prod.snd
  let time := (P.image Prod.snd).max' timesNonempty
  have timeMember : time ∈ P.image Prod.snd := Finset.max'_mem _ _
  obtain ⟨u, hu, timeEq⟩ := Finset.mem_image.mp timeMember
  have rowNonempty : (keysAt P time).Nonempty :=
    ⟨u.1, (mem_keysAt P time u.1).mpr (by simpa only [← timeEq, Prod.eta] using hu)⟩
  let a := (keysAt P time).min' rowNonempty
  let b := (keysAt P time).max' rowNonempty
  have ha : (a, time) ∈ P := (mem_keysAt P time a).mp (Finset.min'_mem _ _)
  have hb : (b, time) ∈ P := (mem_keysAt P time b).mp (Finset.max'_mem _ _)
  have latest : LatestRow P time := fun p hp =>
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  refine ⟨(a, time), (b, time), ⟨⟨ha, fun p hp _ => latest p hp⟩, ?_⟩,
    ⟨⟨hb, fun p hp _ => latest p hp⟩, ?_⟩, latest, rfl⟩
  · intro p hp same
    change p.2 = time at same
    exact Finset.min'_le _ _ ((mem_keysAt P time p.1).mpr (by simpa only [← same, Prod.eta] using hp))
  · intro p hp same
    change p.2 = time at same
    exact Finset.le_max' _ _ ((mem_keysAt P time p.1).mpr (by simpa only [← same, Prod.eta] using hp))

/-- A left-external non-corner is strictly left of the latest left corner. -/
theorem left_before_corner {P : Finset Point} (satisfied : ASS P) {q p : Point}
    (external : LeftExternal P q) (notTop : ¬ LatestRow P q.2)
    (member : p ∈ P) (latest : LatestRow P p.2) : q.1 < p.1 := by
  have newer : q.2 < p.2 := by
    have lower := latest q external.1.1
    by_contra h
    have same : p.2 = q.2 := by omega
    exact notTop (by simpa only [same] using latest)
  by_contra side
  have same := left_quadrant satisfied external member (by omega) newer.le
  have stamp := congrArg Prod.snd same
  omega

theorem right_after_corner {P : Finset Point} (satisfied : ASS P) {q p : Point}
    (external : RightExternal P q) (notTop : ¬ LatestRow P q.2)
    (member : p ∈ P) (latest : LatestRow P p.2) : p.1 < q.1 := by
  have newer : q.2 < p.2 := by
    have lower := latest q external.1.1
    by_contra h
    have same : p.2 = q.2 := by omega
    exact notTop (by simpa only [same] using latest)
  by_contra side
  have same := right_quadrant satisfied external member (by omega) newer.le
  have stamp := congrArg Prod.snd same
  omega

end RotationBST.Geometric.GreedyASS.Items
