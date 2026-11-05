module

public import RotationBST.Algorithms.GreedyASS.Potential.Forest
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Potential
open Items Reference

theorem internal_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (internal : Internal P q) :
    color t lo searches P q = some .red ∧ value t lo searches P q = red t lo P q := by
  simp [color, value, internal.1, internal.2.1, internal.2.2]

/-- Glancing ties are purple, while the selected value is the minimum of
the red and historical purple candidates. -/
theorem glancing_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (glancing : Glancing P q) :
    color t lo searches P q =
        (if red t lo P q < (purple t lo searches q.2 q.1 : WithTop Nat) then some .red else some .purple) ∧
      value t lo searches P q = min (red t lo P q) (purple t lo searches q.2 q.1 : WithTop Nat) := by
  have active : Active P q := glancing.elim (fun h => h.1) (fun h => h.1)
  have nonexternal : ¬ External P q := glancing.elim (fun h => h.2.1) (fun h => h.2.1)
  constructor
  · simp [color, active, nonexternal, glancing]
  · by_cases smaller : red t lo P q < (purple t lo searches q.2 q.1 : WithTop Nat)
    · simp [value, color, active, nonexternal, glancing, smaller, min_eq_left smaller.le]
    · simp [value, color, active, nonexternal, glancing, smaller, min_eq_right (le_of_not_gt smaller)]

/-- Non-corner external ties are green. The point set determines top
corners, including before the new row is added in Phase I. -/
theorem external_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (external : External P q) :
    color t lo searches P q =
        (if LatestRow P q.2 then some .blue
         else if green t lo P q.1 ≤ (currentBlue t lo searches q.1 : WithTop Nat)
           then some .green else some .blue) ∧
      value t lo searches P q =
        (if LatestRow P q.2 then (currentBlue t lo searches q.1 : WithTop Nat)
         else min (green t lo P q.1) (currentBlue t lo searches q.1 : WithTop Nat)) := by
  have active : Active P q := external.elim (fun h => h.1) (fun h => h.1)
  constructor
  · simp [color, active, external]
  · by_cases corner : LatestRow P q.2
    · simp [value, color, active, external, corner]
    · by_cases smaller : green t lo P q.1 ≤ (currentBlue t lo searches q.1 : WithTop Nat)
      · simp [value, color, active, external, corner, smaller]
      · simp [value, color, active, external, corner, smaller, min_eq_right (le_of_not_ge smaller)]

theorem corner_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (external : External P q) (latest : LatestRow P q.2) :
    color t lo searches P q = some .blue ∧
      value t lo searches P q = WithTop.some (currentBlue t lo searches q.1) := by
  simpa only [latest, ↓reduceIte] using external_spec t lo searches external

/-- An actual green item is external but is not on the latest point row.
This exclusion remains valid at the intermediate snapshot. -/
theorem green_spec (t : Tree) (lo : Nat) (searches : List Nat) {P : Finset Point} {q : Point}
    (colored : color t lo searches P q = some .green) :
    External P q ∧ ¬ LatestRow P q.2 ∧
      green t lo P q.1 ≤ WithTop.some (currentBlue t lo searches q.1) ∧
      value t lo searches P q = green t lo P q.1 := by
  have active : Active P q := by
    by_contra inactive
    simp only [color, inactive, not_false_eq_true, ↓reduceIte] at colored
    contradiction
  have external : External P q := by
    by_contra nonexternal
    simp only [color, active, not_true_eq_false, ↓reduceIte, nonexternal] at colored
    split at colored
    · split at colored <;> contradiction
    · contradiction
  have spec := (external_spec t lo searches external).1
  have notTop : ¬ LatestRow P q.2 := by
    intro latest
    rw [(corner_spec t lo searches external latest).1] at colored
    contradiction
  rw [ite_eq_right notTop] at spec
  have below : green t lo P q.1 ≤ WithTop.some (currentBlue t lo searches q.1) := by
    by_contra above
    simp only [above, ↓reduceIte] at spec
    rw [spec] at colored
    contradiction
  exact ⟨external, notTop, below, by simp only [value, colored]⟩

/-- Infinite candidates never become infinite selected item potentials. -/
theorem finite (t : Tree) (lo : Nat) (searches : List Nat) (P : Finset Point) (q : Point) :
    ∃ v : Nat, value t lo searches P q = v := by
  by_cases active : Active P q
  · by_cases external : External P q
    · rw [(external_spec t lo searches external).2]
      split
      · exact ⟨_, rfl⟩
      · cases green t lo P q.1 using WithTop.recTopCoe with
        | top => exact ⟨currentBlue t lo searches q.1, by simp⟩
        | coe g => exact ⟨min g (currentBlue t lo searches q.1), by simp⟩
    · obtain ⟨a, b, _, _, _, _, eq⟩ := red_finite t lo active external
      by_cases glancing : Glancing P q
      · rw [(glancing_spec t lo searches glancing).2, eq]
        exact ⟨min (Distance.toLCA t lo q.1 a b) (purple t lo searches q.2 q.1), by simp⟩
      · rw [(internal_spec t lo searches ⟨active, external, glancing⟩).2, eq]
        exact ⟨_, rfl⟩
  · exact ⟨0, by simp [value, color, active]⟩

/-- The internal case of Lemma 3.17, at a fixed reference-history snapshot. -/
theorem internal_unchanged (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {q : Point} (internal : Internal P q) (untouched : q.1 ∉ keys) :
    value t lo searches (P ∪ row time keys) q = value t lo searches P q := by
  rw [(internal_spec t lo searches (Items.internal_unchanged keys history internal untouched)).2,
    (internal_spec t lo searches internal).2]
  exact red_unchanged t lo keys history internal.1.1

/-- If an unaccessed glancing point stays glancing, neither its selected
color nor its potential changes during Phase II. -/
theorem glancing_unchanged (t : Tree) (lo : Nat) (searches : List Nat)
    {n time : Nat} {P : Finset Point} (keys : Finset Nat) (history : History n time P)
    {q : Point} (old : Glancing P q) (new : Glancing (P ∪ row time keys) q) :
    color t lo searches (P ∪ row time keys) q = color t lo searches P q ∧
      value t lo searches (P ∪ row time keys) q = value t lo searches P q := by
  have member : q ∈ P := old.elim (fun h => h.1.1) (fun h => h.1.1)
  have unchanged := red_unchanged t lo keys history member
  rw [(glancing_spec t lo searches new).1, (glancing_spec t lo searches old).1,
    (glancing_spec t lo searches new).2, (glancing_spec t lo searches old).2, unchanged]
  exact ⟨rfl, rfl⟩

end RotationBST.Geometric.GreedyASS.Potential
