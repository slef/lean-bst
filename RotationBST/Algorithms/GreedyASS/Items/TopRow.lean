module

public import RotationBST.Algorithms.GreedyASS.Items.Updates
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Items

private theorem time_le {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {p : Point} (member : p ∈ P ∪ row time keys) : p.2 ≤ time := by
  rcases Finset.mem_union.mp member with old | current
  · exact Nat.le_of_lt (history p old).2
  · exact le_of_eq ((mem_row p time keys).mp current).2

/-- Adding a later row makes that row latest, independently of the
reference-search history used to evaluate potentials. -/
theorem top_latest {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) : LatestRow (P ∪ row time keys) time :=
  fun _ hp => time_le keys history hp

/-- On a completed nonempty row, the geometric latest-row test agrees with
the row's timestamp. During Phase I it keeps referring to the old row. -/
theorem latest_row_iff {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) (nonempty : keys.Nonempty) {q : Point}
    (member : q ∈ P ∪ row time keys) : LatestRow (P ∪ row time keys) q.2 ↔ q.2 = time := by
  constructor
  · intro latest
    obtain ⟨x, hx⟩ := nonempty
    have lower := latest (x, time) (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hx, rfl⟩))
    have upper := time_le keys history member
    omega
  · intro same
    rw [same]
    exact top_latest keys history

theorem top_active {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys) :
    Active (P ∪ row time keys) (x, time) :=
  ⟨Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨member, rfl⟩),
    fun _ hp _ => time_le keys history hp⟩

theorem top_left {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys) :
    LeftExternal (P ∪ row time keys) (x, time) ↔ ∀ y ∈ keys, x ≤ y := by
  constructor
  · intro external y hy
    exact external.2 (y, time) (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hy, rfl⟩)) rfl
  · intro first
    refine ⟨top_active keys history member, ?_⟩
    intro p hp same
    rcases Finset.mem_union.mp hp with hp | hp
    · have := (history p hp).2
      change p.2 = time at same
      omega
    · exact first p.1 ((mem_row p time keys).mp hp).1

theorem top_right {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys) :
    RightExternal (P ∪ row time keys) (x, time) ↔ ∀ y ∈ keys, y ≤ x := by
  constructor
  · intro external y hy
    exact external.2 (y, time) (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨hy, rfl⟩)) rfl
  · intro last
    refine ⟨top_active keys history member, ?_⟩
    intro p hp same
    rcases Finset.mem_union.mp hp with hp | hp
    · have := (history p hp).2
      change p.2 = time at same
      omega
    · exact last p.1 ((mem_row p time keys).mp hp).1

/-- Every nonexternal new access is glancing in both directions. -/
theorem top_glancing {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys)
    (nonexternal : ¬ External (P ∪ row time keys) (x, time)) :
    LeftGlancing (P ∪ row time keys) (x, time) ∧ RightGlancing (P ∪ row time keys) (x, time) := by
  have noLater : ∀ p ∈ P ∪ row time keys, ¬ time < p.2 := by
    intro p hp later
    have := time_le keys history hp
    omega
  exact ⟨⟨top_active keys history member, nonexternal, fun p hp later => (noLater p hp later).elim⟩,
    ⟨top_active keys history member, nonexternal, fun p hp later => (noLater p hp later).elim⟩⟩

theorem top_classification {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) {x : Nat} (member : x ∈ keys) :
    (External (P ∪ row time keys) (x, time) ∨ Glancing (P ∪ row time keys) (x, time)) ∧
      ¬ Internal (P ∪ row time keys) (x, time) := by
  have cases : External (P ∪ row time keys) (x, time) ∨ Glancing (P ∪ row time keys) (x, time) := by
    by_cases external : External (P ∪ row time keys) (x, time)
    · exact Or.inl external
    · exact Or.inr (Or.inl (top_glancing keys history member external).1)
  refine ⟨cases, ?_⟩
  intro internal
  rcases cases with external | glancing
  · exact internal.2.1 external
  · exact internal.2.2 glancing

/-- Only the two extreme accesses can be external on the newest row. -/
theorem corners_bound {n time : Nat} {P : Finset Point} (keys : Finset Nat)
    (history : History n time P) : (corners P time keys).card ≤ 2 := by
  rcases keys.eq_empty_or_nonempty with rfl | nonempty
  · simp [corners]
  have covered : corners P time keys ⊆ {keys.min' nonempty, keys.max' nonempty} := by
    intro x hx
    obtain ⟨member, left | right⟩ := Finset.mem_filter.mp hx
    · have least := (top_left keys history member).mp left
      have eq : x = keys.min' nonempty := le_antisymm
        (least _ (Finset.min'_mem _ nonempty)) (Finset.min'_le _ _ member)
      simp [eq]
    · have greatest := (top_right keys history member).mp right
      have eq : x = keys.max' nonempty := le_antisymm (Finset.le_max' _ _ member)
        (greatest _ (Finset.max'_mem _ nonempty))
      simp [eq]
  exact (Finset.card_le_card covered).trans Finset.card_le_two

end RotationBST.Geometric.GreedyASS.Items
