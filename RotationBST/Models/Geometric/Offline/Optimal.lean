module

public import RotationBST.Models.Geometric.Offline.Proofs
import Mathlib.Data.Nat.Find

@[expose] public section
namespace RotationBST.Geometric

theorem request_time {p : Point} (time : Nat) (xs : List Nat)
    (h : p ∈ requestsAt time xs) : time ≤ p.2 ∧ p.2 < time + xs.length := by
  induction xs generalizing time with
  | nil => simp [requestsAt] at h
  | cons x xs ih =>
    rcases Finset.mem_insert.mp h with rfl | h
    · simp only [List.length_cons]; omega
    · have := ih (time + 1) h
      simp only [List.length_cons]
      omega

theorem requests_card (time : Nat) (xs : List Nat) :
    (requestsAt time xs).card = xs.length := by
  induction xs generalizing time with
  | nil => simp [requestsAt]
  | cons x xs ih =>
    rw [requestsAt, Finset.card_insert_of_notMem, ih]
    · rfl
    · intro h
      have := request_time (time + 1) xs h
      omega

theorem offline_lower_bound {n : Nat} {xs : List Nat} (E : Offline n xs) :
    xs.length ≤ E.points.card := by
  rw [← requests_card 0 xs]
  exact Finset.card_le_card E.contains

theorem offline_minimum {n : Nat} (xs : List Nat) (valid : ∀ x ∈ xs, x < n) :
    ∃ E : Offline n xs, ∀ F : Offline n xs, E.points.card ≤ F.points.card := by
  classical
  let A : OnlineAlgorithm n := ⟨greedySweep, fun _ _ _ => sweep_correct⟩
  obtain ⟨E, _, _⟩ := offline_of_online A xs valid
  have existsCost : ∃ k : Nat, ∃ E : Offline n xs, E.points.card = k :=
    ⟨E.points.card, E, rfl⟩
  obtain ⟨F, hf⟩ := Nat.find_spec existsCost
  refine ⟨F, fun G => ?_⟩
  rw [hf]
  exact Nat.find_min' existsCost ⟨G, rfl⟩

end RotationBST.Geometric
