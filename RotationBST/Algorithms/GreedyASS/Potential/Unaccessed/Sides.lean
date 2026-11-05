module

public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.ExactNeighbors
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.Unaccessed
open Items Reference

/-- If a left-external item is not accessed, every access is strictly on
its right. The old point blocks projections crossing to its left. -/
theorem left_side {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {q : Point}
    (external : LeftExternal P q) (untouched : q.1 ∉ greedySweep time searched P) :
    ∀ y ∈ greedySweep time searched P, q.1 < y := by
  have searchRight : q.1 < searched := by
    by_contra side
    exact untouched (Accessed.left_access satisfied external time searched
      (history q external.1.1).2.le (by omega))
  intro y member
  by_contra side
  have yq : y < q.1 := by
    have different : y ≠ q.1 := by intro eq; subst y; exact untouched member
    omega
  obtain ⟨stamp, active⟩ := Accessed.accessed_active member (by omega)
  have earlier := Accessed.left_time satisfied active external yq
  have visible := Accessed.access_visible history active member (by simp only; omega)
  apply visible.2 q external.1.1 (by intro eq; have := congrArg Prod.fst eq; simp only at this; omega)
  simp only [Rectangle]
  exact ⟨(min_le_left _ _).trans yq.le, searchRight.le.trans (le_max_right _ _),
    (min_le_left _ _).trans earlier.le, (history q external.1.1).2.le.trans (le_max_right _ _)⟩

theorem right_side {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {q : Point}
    (external : RightExternal P q) (untouched : q.1 ∉ greedySweep time searched P) :
    ∀ y ∈ greedySweep time searched P, y < q.1 := by
  have searchLeft : searched < q.1 := by
    by_contra side
    exact untouched (Accessed.right_access satisfied external time searched
      (history q external.1.1).2.le (by omega))
  intro y member
  by_contra side
  have qy : q.1 < y := by
    have different : y ≠ q.1 := by intro eq; subst y; exact untouched member
    omega
  obtain ⟨stamp, active⟩ := Accessed.accessed_active member (by omega)
  have earlier := Accessed.right_time satisfied active external qy
  have visible := Accessed.access_visible history active member (by simp only; omega)
  apply visible.2 q external.1.1 (by intro eq; have := congrArg Prod.fst eq; simp only at this; omega)
  simp only [Rectangle]
  exact ⟨(min_le_right _ _).trans searchLeft.le, qy.le.trans (le_max_left _ _),
    (min_le_left _ _).trans earlier.le, (history q external.1.1).2.le.trans (le_max_right _ _)⟩

theorem one_side {n time searched : Nat} {P : Finset Point}
    (satisfied : ASS P) (history : History n time P) {q : Point}
    (external : External P q) (untouched : q.1 ∉ greedySweep time searched P) :
    (∀ y ∈ greedySweep time searched P, y < q.1) ∨
      (∀ y ∈ greedySweep time searched P, q.1 < y) := by
  rcases external with left | right
  · exact Or.inr (left_side satisfied history left untouched)
  · exact Or.inl (right_side satisfied history right untouched)

end RotationBST.Geometric.GreedyASS.Potential.Unaccessed
