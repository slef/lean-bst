module

public import RotationBST.Algorithms.GreedyASS.Potential.PhaseOne.Blue
public import Mathlib.Algebra.Order.Monoid.WithTop
public import RotationBST.Algorithms.GreedyASS.Potential.Accessed.Accounting
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential.PhaseOne
open Items Reference

theorem select_finite (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) (b : Nat) :
    ∃ v : Nat, select t lo searches P q b = WithTop.some v := by
  by_cases active : Active P q
  · by_cases external : External P q
    · simp only [select, active, not_true_eq_false, ite_false, external, ite_true]
      split
      · exact ⟨b, rfl⟩
      · cases green t lo P q.1 using WithTop.recTopCoe with
        | top => exact ⟨b, by simp⟩
        | coe g => exact ⟨min g b, by simp⟩
    · obtain ⟨a, c, _, _, _, _, eq⟩ := red_finite t lo active external
      simp only [select, active, not_true_eq_false, ite_false, external, eq]
      split
      · exact ⟨min (Distance.toLCA t lo q.1 a c) (max (purple t lo searches q.2 q.1) b), by simp⟩
      · exact ⟨_, rfl⟩
  · exact ⟨0, by simp [select, active]⟩

theorem amount_exact (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point)
    (roots : List Component) (x : Nat) : itemAt t lo searches P roots x = WithTop.some (amountAt t lo searches P roots x) := by
  have finite : ∃ v : Nat, itemAt t lo searches P roots x = WithTop.some v := by
    cases recent : latest P x with
    | none => exact ⟨0, by simp [itemAt, recent]⟩
    | some stamp =>
      obtain ⟨v, value⟩ := select_finite t lo searches P (x, stamp) (rootBlue roots x)
      exact ⟨v, by simpa only [itemAt, recent, valueAt] using value⟩
  obtain ⟨v, eq⟩ := finite
  simp only [amountAt, eq]
  rfl

/-- With geometry and historical floor fixed, the selected potential is
monotone in the current blue candidate. -/
theorem select_mono (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point)
    {a b : Nat} (le : a ≤ b) : select t lo searches P q a ≤ select t lo searches P q b := by
  simp only [select]
  split
  · exact le_rfl
  · split
    · split
      · exact WithTop.coe_le_coe.mpr le
      · exact min_le_min_left _ (WithTop.coe_le_coe.mpr le)
    · split
      · exact min_le_min_left _ (WithTop.coe_le_coe.mpr (max_le_max_left _ le))
      · exact le_rfl

private theorem min_increment (cap : WithTop Nat) {a b : Nat} (bound : b ≤ a + 1) :
    min cap (WithTop.some b) ≤ min cap (WithTop.some a) + 1 := by
  by_cases capped : cap ≤ WithTop.some a
  · rw [min_eq_left capped]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (by simp))
  · rw [min_eq_right (le_of_not_ge capped)]
    exact (min_le_right _ _).trans (by simpa only [WithTop.coe_add, WithTop.coe_one] using (WithTop.coe_le_coe.mpr bound))

/-- Raising the root distance by at most one raises selected value by at
most one, even if a min/max threshold changes which candidate is selected. -/
theorem select_increment (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point)
    {a b : Nat} (bound : b ≤ a + 1) : select t lo searches P q b ≤ select t lo searches P q a + 1 := by
  simp only [select]
  split
  · simp
  · split
    · split
      · simpa only [WithTop.coe_add, WithTop.coe_one] using (WithTop.coe_le_coe.mpr bound)
      · exact min_increment _ bound
    · split
      · apply min_increment
        omega
      · exact le_add_of_nonneg_right (by simp)

/-- An insensitive point is already capped by a geometry-only candidate,
so no new blue value can increase its selected potential. -/
theorem select_capped (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point)
    (a b : Nat) (insensitive : ¬ Sensitive t lo P q a) :
    select t lo searches P q b ≤ select t lo searches P q a := by
  by_cases active : Active P q
  · by_cases external : External P q
    · have notTop : ¬ LatestRow P q.2 := fun top => insensitive (Or.inl ⟨external, Or.inl top⟩)
      have capped : green t lo P q.1 ≤ WithTop.some a := by
        apply le_of_not_gt
        intro greater
        exact insensitive (Or.inl ⟨external, Or.inr greater⟩)
      simp only [select, active, not_true_eq_false, ite_false, external, ite_true, notTop, min_eq_left capped]
      exact min_le_left _ _
    · by_cases glancing : Glancing P q
      · have capped : red t lo P q ≤ WithTop.some a := by
          apply le_of_not_gt
          intro greater
          exact insensitive (Or.inr ⟨glancing, greater⟩)
        have floor : red t lo P q ≤ WithTop.some (max (purple t lo searches q.2 q.1) a) :=
          capped.trans (WithTop.coe_le_coe.mpr (le_max_right _ _))
        simp only [select, active, not_true_eq_false, ite_false, external, glancing, ite_true, min_eq_left floor]
        exact min_le_left _ _
      · simp only [select, active, not_true_eq_false, ite_false, external, glancing, le_refl]
  · simp [select, active]

/-- The unit charge is needed only on the explicitly defined sensitive set. -/
theorem select_charge (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point)
    {a b : Nat} (bound : b ≤ a + 1) :
    select t lo searches P q b ≤ select t lo searches P q a +
      WithTop.some (if Sensitive t lo P q a then 1 else 0) := by
  by_cases sensitive : Sensitive t lo P q a
  · simpa only [sensitive, ite_true, WithTop.coe_one] using select_increment t lo searches P q bound
  · simpa only [sensitive, ite_false, WithTop.coe_zero, add_zero] using select_capped t lo searches P q a b sensitive

end RotationBST.Geometric.GreedyASS.Potential.PhaseOne
