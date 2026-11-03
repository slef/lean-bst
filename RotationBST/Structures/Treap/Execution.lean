module

public import RotationBST.Structures.Treap.Step
public import RotationBST.Structures.Treap.Existence
public import RotationBST.Models.Pointer.Simulation

@[expose] public section
namespace RotationBST.Arboral

theorem treap_execution {P : Finset Point} (sat : ASS P) (time : Nat)
    (t : Tree) (heap : Heap (nextTouch P time) t 0)
    (bounded : ∀ p ∈ P, p.1 < t.size) (xs : List Nat)
    (requests : requestsAt time xs ⊆ P) :
    ∃ u cost, u.size = t.size ∧ Heap (nextTouch P (time + xs.length)) u 0 ∧
      Pointer.Execution t xs u cost ∧
      cost + 33 * scheduleCost P time ≤ 33 * scheduleCost P (time + xs.length) := by
  induction xs generalizing time t with
  | nil => exact ⟨t, 0, rfl, by simpa using heap, .nil, by simp⟩
  | cons x xs ih =>
    have req : (x, time) ∈ P := requests (Finset.mem_insert_self ..)
    obtain ⟨v, c, hv, hh, hs, hc⟩ := treap_step sat t heap bounded req
    have boundV : ∀ p ∈ P, p.1 < v.size := by simpa only [hv] using bounded
    have reqs : requestsAt (time + 1) xs ⊆ P :=
      fun _ h => requests (Finset.mem_insert_of_mem h)
    obtain ⟨u, d, hu, hheap, hex, hcost⟩ := ih (time + 1) v hh boundV reqs
    refine ⟨u, c + d, hu.trans hv, ?_, .cons hs hex, ?_⟩
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hheap
    · simp only [scheduleCost, Nat.mul_add] at hcost
      have heq : time + (x :: xs).length = time + 1 + xs.length := by simp; omega
      rw [heq]
      omega

/-- An offline ASS solution yields a genuine pointer execution. The initial
tree is existential: it is chosen using the future-priority treap. -/
theorem offline_to_pointer {n : Nat} {xs : List Nat} (E : Offline n xs) :
    ∃ s t cost, s.size = n ∧ Pointer.Execution s xs t cost ∧ cost ≤ 33 * E.points.card := by
  obtain ⟨s, hsize, heap⟩ := heap_exists (nextTouch E.points 0) n 0
  have bounded : ∀ p ∈ E.points, p.1 < s.size := by
    intro p hp
    rw [hsize]
    exact (E.bounded p hp).1
  obtain ⟨t, cost, _, _, he, hc⟩ := treap_execution E.satisfied 0 s heap bounded xs E.contains
  refine ⟨s, t, cost, hsize, he, ?_⟩
  simpa only [scheduleCost, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    bounded_schedule_cost E.bounded] using hc

/-- The same construction in the simplified model, charging the final pending
rotations explicitly. The request charge is included in the bound. -/
theorem offline_to_rotations {n : Nat} {xs : List Nat} (E : Offline n xs) :
    ∃ s u t rotations pending, s.size = n ∧
      RotationBST.Execution s xs u rotations ∧ Rotations u t pending ∧
      xs.length + rotations + pending ≤ 99 * E.points.card := by
  obtain ⟨s, t, cost, hsize, he, hc⟩ := offline_to_pointer E
  obtain ⟨u, rotations, pending, he', hp, hb⟩ := Pointer.execution_to_rotations he
  exact ⟨s, u, t, rotations, pending, hsize, he', hp, by omega⟩

end RotationBST.Arboral
