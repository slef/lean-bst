module

public import RotationBST.Algorithms.Simulation.LastTouch.Defs
public import RotationBST.Models.Region.View.History
public import RotationBST.Algorithms.GreedyASS.Sweep

public import RotationBST.Algorithms.GreedyASS.Algorithm.Abstract

@[expose] public section
namespace RotationBST.Geometric

/-- Appending a row raises precisely its keys to the new maximum priority. -/
theorem lastTouch_extend {n time : Nat} {P : Finset Point} (hist : History n time P)
    (keys : Finset Nat) (key : Nat) :
    lastTouch (P ∪ row time keys) key = if key ∈ keys then (time : WithBot Nat) else lastTouch P key := by
  by_cases member : key ∈ keys
  · rw [ite_eq_left member]
    exact last_new_current hist member
  · rw [ite_eq_right member]
    exact last_new_untouched member

/-- Every nonbottom priority is attained by a point in the supplied history. -/
theorem lastTouch_attained {P : Finset Point} {key : Nat} (positive : ⊥ < lastTouch P key) :
    ∃ time, (key, time) ∈ P ∧ lastTouch P key = (time : WithBot Nat) := by
  obtain ⟨time, equal⟩ := WithBot.ne_bot_iff_exists.mp (ne_of_gt positive)
  have member := Finset.mem_of_max equal.symm
  obtain ⟨p, hp, timeEqual⟩ := Finset.mem_image.mp member
  obtain ⟨hp, keyEqual⟩ := Finset.mem_filter.mp hp
  have pointEqual : p = (key, time) := Prod.ext keyEqual timeEqual
  exact ⟨time, pointEqual ▸ hp, equal.symm⟩

/-- A last-touch boundary makes an empty old rectangle with the new access. -/
theorem boundary_visible {n time boundary key : Nat} {P : Finset Point}
    (hist : History n time P) (dominates : LastTouchBoundary P boundary key) :
    ∃ old, (boundary, old) ∈ P ∧ Visible P time key (boundary, old) := by
  obtain ⟨old, member, latest⟩ := lastTouch_attained dominates.2.1
  refine ⟨old, member, dominates.1, ?_⟩
  intro p hp different rectangle
  have oldBefore : old < time := (hist _ member).2
  have lower : old ≤ p.2 := by
    have h := rectangle.2.2.1
    simp only [min_eq_left (Nat.le_of_lt oldBefore)] at h
    exact h
  have prior : (p.2 : WithBot Nat) ≤ lastTouch P p.1 :=
    touch_le_last (by simpa only [Prod.eta] using hp)
  by_cases same : p.1 = boundary
  · have upper : p.2 ≤ old := by
      rw [same, latest] at prior
      exact_mod_cast prior
    exact different (Prod.ext same (by omega))
  · have strict := dominates.2.2 p.1 rectangle.1 rectangle.2.1 same
    rw [latest] at strict
    have lower' : (old : WithBot Nat) ≤ p.2 := by exact_mod_cast lower
    exact (not_lt_of_ge (lower'.trans prior)) strict

/-- Touching a key forces each dominating last-touch boundary onto this row.
This is the geometric invariant used to traverse the online supernode treap. -/
theorem boundary_required {n time request boundary key : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (completion : Completion n time request P keys)
    (touched : key ∈ keys) (dominates : LastTouchBoundary P boundary key) : boundary ∈ keys := by
  obtain ⟨old, member, visible⟩ := boundary_visible hist dominates
  apply sweep_subset hist (show Completion n time key P keys from ⟨touched, completion.2⟩)
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(boundary, old), Finset.mem_filter.mpr ⟨member, visible⟩, rfl⟩

end RotationBST.Geometric
