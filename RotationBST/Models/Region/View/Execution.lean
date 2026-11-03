module

public import RotationBST.Models.Region.View.Preservation
public import RotationBST.Models.Geometric.Offline.Proofs

@[expose] public section
namespace RotationBST.Arboral

theorem region_execution_view {s t : Tree} {xs : List Nat} {cost n : Nat}
    (execution : RegionExecution s xs t cost) (size : s.size = n)
    (time : Nat) (P : Finset Point) (hist : History n time P) (sat : ASS P)
    (heap : HistoryHeap P s) :
    ∃ Q, ASS Q ∧ History n (time + xs.length) Q ∧ HistoryHeap Q t ∧
      requestsAt time xs ⊆ Q ∧ P ⊆ Q ∧ Q.card = P.card + cost := by
  induction execution generalizing time P with
  | nil => exact ⟨P, sat, by simpa using hist, heap, by simp [requestsAt],
      fun _ h => h, by simp⟩
  | @cons s v t x cost xs step tail ih =>
    have same := Region.same_of_fringe step.fringe 0
    have ssize : step.before.tree.size = n := by rw [step.source, size]
    have vsize : v.size = n := by rw [← step.target, ← same.1]; exact ssize
    have sheap : HistoryHeap P step.before.tree := by simpa only [step.source] using heap
    have completion : Completion n time x P (Region.keys step.before 0) := by
      refine ⟨step.visits, ?_, region_ass sat hist step.before ssize sheap⟩
      intro key hk
      have h := Region.keys_bounds hk
      exact Finset.mem_range.mpr (by simpa only [Nat.zero_add, ssize] using h.2)
    have newHeap : HistoryHeap (P ∪ row time (Region.keys step.before 0)) v := by
      simpa only [step.target] using region_history_heap hist same sheap
    obtain ⟨Q, hsat, hhist, hheap, hreq, hsub, hcard⟩ := ih vsize (time + 1)
      (P ∪ row time (Region.keys step.before 0)) (history_extend hist completion)
      completion.2.2 newHeap
    refine ⟨Q, hsat, ?_, hheap, ?_, Finset.subset_union_left.trans hsub, ?_⟩
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhist
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hsub (Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨step.visits, rfl⟩))
      · exact hreq hp
    · rw [completion_card hist completion, Region.keys_card] at hcard
      simpa only [Nat.add_assoc] using hcard

theorem historyHeap_empty (s : Tree) : HistoryHeap ∅ s := by
  have all : ∀ lo, Heap (fun key => OrderDual.toDual (lastTouch ∅ key)) s lo := by
    induction s with
    | nil => intro _; trivial
    | node l r il ir =>
      intro lo
      exact ⟨fun _ _ => by simp [lastTouch], il lo, ir (lo + l.size + 1)⟩
  exact all 0

/-- Every region execution has an ASS view with exactly its charged cost. -/
theorem region_to_offline {s t : Tree} {xs : List Nat} {cost : Nat}
    (execution : RegionExecution s xs t cost) :
    ∃ E : Offline s.size xs, E.points.card = cost := by
  have hist : History s.size 0 ∅ := by simp [History]
  obtain ⟨Q, sat, bound, _, requests, _, card⟩ :=
    region_execution_view execution rfl 0 ∅ hist ass_empty (historyHeap_empty s)
  exact ⟨⟨⟨Q, requests, sat⟩, by simpa using bound⟩, by simpa using card⟩

end RotationBST.Arboral
