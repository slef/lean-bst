module

public import RotationBST.Models.Equivalence.Offline

@[expose] public section
namespace RotationBST.Geometric

private theorem treap_regions {P : Finset Point} (sat : ASS P) (time : Nat)
    (t : Tree) (heap : Heap (nextTouch P time) t 0)
    (bounded : ∀ p ∈ P, p.1 < t.size) (xs : List Nat)
    (requests : requestsAt time xs ⊆ P) :
    ∃ u cost, RegionExecution t xs u cost ∧
      cost + scheduleCost P time = scheduleCost P (time + xs.length) := by
  induction xs generalizing time t with
  | nil => exact ⟨t, 0, .nil, by simp⟩
  | cons x xs ih =>
    obtain ⟨v, step, hv, hh, hc⟩ := treap_region_step sat t heap bounded
      (requests (Finset.mem_insert_self ..))
    obtain ⟨u, cost, execution, charge⟩ := ih (time + 1) v hh
      (by simpa only [hv] using bounded) (fun _ h => requests (Finset.mem_insert_of_mem h))
    refine ⟨u, step.before.size + cost, .cons step execution, ?_⟩
    simp only [scheduleCost] at charge
    have heq : time + (x :: xs).length = time + 1 + xs.length := by simp; omega
    rw [heq]
    omega

theorem offline_to_regions {n : Nat} {xs : List Nat} (E : Offline n xs) :
    ∃ s t, s.size = n ∧ RegionExecution s xs t E.points.card := by
  obtain ⟨s, hsize, heap⟩ := heap_exists (nextTouch E.points 0) n 0
  obtain ⟨t, cost, execution, charge⟩ := treap_regions E.satisfied 0 s heap
    (by intro p hp; rw [hsize]; exact (E.bounded p hp).1) xs E.contains
  have heq : cost = E.points.card := by
    simpa only [scheduleCost, Nat.zero_add, Nat.add_zero, bounded_schedule_cost E.bounded] using charge
  exact ⟨s, t, hsize, heq ▸ execution⟩

/-- Exact cost equivalence with the paper's rooted-subtree model, with a freely
chosen initial tree. Constants enter only when changing operation models. -/
theorem offline_iff_regions (n : Nat) (xs : List Nat) (cost : Nat) :
    (∃ E : Offline n xs, E.points.card = cost) ↔
      ∃ s t, s.size = n ∧ RegionExecution s xs t cost := by
  constructor
  · rintro ⟨E, rfl⟩
    exact offline_to_regions E
  · rintro ⟨s, t, hsize, execution⟩
    obtain ⟨E, hcard⟩ := region_to_offline execution
    subst n
    exact ⟨E, hcard⟩

end RotationBST.Geometric
