module

public import RotationBST.Algorithms.GreedyASS.Barrier.Steps
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Geometric.GreedyASS.Barrier

/-- Arbitrarily many near-side requests preserve the same barrier and the
entire old point set on its far side. Requests may equal the barrier key. -/
theorem fill_left {P : Finset Point} {key stamp time : Nat} (xs : List Nat)
    (barrier : Left P key stamp) (later : stamp ≤ time)
    (side : ∀ x ∈ xs, key ≤ x) :
    Left (fill greedySweep time P xs) key stamp ∧
      ∀ p : Point, p.1 < key → (p ∈ fill greedySweep time P xs ↔ p ∈ P) := by
  induction xs generalizing time P with
  | nil => exact ⟨barrier, fun _ _ => Iff.rfl⟩
  | cons x xs ih =>
    obtain ⟨next, same⟩ := step_left barrier later (side x (by simp))
    obtain ⟨final, frozen⟩ := ih (time := time + 1) next (by omega)
      (fun y hy => side y (by simp [hy]))
    exact ⟨final, fun p far => (frozen p far).trans (same p far)⟩

theorem fill_right {P : Finset Point} {key stamp time : Nat} (xs : List Nat)
    (barrier : Right P key stamp) (later : stamp ≤ time)
    (side : ∀ x ∈ xs, x ≤ key) :
    Right (fill greedySweep time P xs) key stamp ∧
      ∀ p : Point, key < p.1 → (p ∈ fill greedySweep time P xs ↔ p ∈ P) := by
  induction xs generalizing time P with
  | nil => exact ⟨barrier, fun _ _ => Iff.rfl⟩
  | cons x xs ih =>
    obtain ⟨next, same⟩ := step_right barrier later (side x (by simp))
    obtain ⟨final, frozen⟩ := ih (time := time + 1) next (by omega)
      (fun y hy => side y (by simp [hy]))
    exact ⟨final, fun p far => (frozen p far).trans (same p far)⟩

/-- Lemma 3.4, left side, for the actual executable GreedyASS stream. An
access on row `stamp` rules out every later far-side access while subsequent
searches stay on or to the right of its key. -/
theorem no_left_access {n key stamp : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P) (accessed : (key, stamp) ∈ P)
    (side : ∀ x ∈ xs, key ≤ x) :
    ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → key ≤ p.1 := by
  have barrier := (fill_left (time := stamp + 1) xs
    (of_history history accessed).1 (by omega) side).1
  intro p hp recent
  by_contra crossed
  have := barrier.2 p hp (by omega)
  omega

theorem no_right_access {n key stamp : Nat} {P : Finset Point} (xs : List Nat)
    (history : History n (stamp + 1) P) (accessed : (key, stamp) ∈ P)
    (side : ∀ x ∈ xs, x ≤ key) :
    ∀ p ∈ fill greedySweep (stamp + 1) P xs, stamp < p.2 → p.1 ≤ key := by
  have barrier := (fill_right (time := stamp + 1) xs
    (of_history history accessed).2 (by omega) side).1
  intro p hp recent
  by_contra crossed
  have := barrier.2 p hp (by omega)
  omega

end RotationBST.Geometric.GreedyASS.Barrier
