module

public import RotationBST.Models.Geometric.Online.Abstract
public import RotationBST.Algorithms.GreedyASS.Sweep

@[expose] public section
namespace RotationBST.Arboral

theorem history_extend {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (hist : History n time P) (h : Completion n time request P keys) :
    History n (time + 1) (P ∪ row time keys) := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact ⟨(hist p hp).1, Nat.lt_succ_of_lt (hist p hp).2⟩
  obtain ⟨hkey, ht⟩ := (mem_row p time keys).mp hp
  exact ⟨Finset.mem_range.mp (h.2.1 hkey), by omega⟩

theorem fill_spec {n : Nat} (A : OnlineAlgorithm n) (time : Nat) (P : Finset Point)
    (xs : List Nat) (hist : History n time P) (sat : ASS P)
    (valid : ∀ x ∈ xs, x < n) :
    ASS (fill A.step time P xs) ∧
    History n (time + xs.length) (fill A.step time P xs) ∧
    (fill A.step time P xs).card = P.card + rowCost A.step time P xs := by
  induction xs generalizing time P with
  | nil => simpa [fill, rowCost] using And.intro sat hist
  | cons x xs ih =>
    have h := A.correct time x P hist sat (valid x (List.mem_cons_self ..))
    obtain ⟨s, h', c⟩ := ih (time + 1) (P ∪ row time (A.step time x P))
      (history_extend hist h) h.2.2 (fun y hy => valid y (List.mem_cons_of_mem _ hy))
    refine ⟨s, ?_, ?_⟩
    · simpa only [fill, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h'
    · change (fill A.step (time + 1) (P ∪ row time (A.step time x P)) xs).card = _
      rw [c, completion_card hist h]
      simp [rowCost, Nat.add_assoc]

theorem fill_mono (step : Nat → Nat → Finset Point → Finset Nat)
    (time : Nat) (P : Finset Point) (xs : List Nat) : P ⊆ fill step time P xs := by
  induction xs generalizing time P with
  | nil => exact fun _ h => h
  | cons x xs ih => exact Finset.subset_union_left.trans (ih _ _)

theorem fill_contains {n : Nat} (A : OnlineAlgorithm n) (time : Nat)
    (P : Finset Point) (xs : List Nat) (hist : History n time P) (sat : ASS P)
    (valid : ∀ x ∈ xs, x < n) : requestsAt time xs ⊆ fill A.step time P xs := by
  induction xs generalizing time P with
  | nil => simp [requestsAt]
  | cons x xs ih =>
    have h := A.correct time x P hist sat (valid x (List.mem_cons_self ..))
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · apply fill_mono A.step (time + 1) (P ∪ row time (A.step time x P)) xs
      exact Finset.mem_union_right _ ((mem_row _ _ _).mpr ⟨h.1, rfl⟩)
    · exact ih _ _ (history_extend hist h) h.2.2
        (fun y hy => valid y (List.mem_cons_of_mem _ hy)) hp

/-- Running a prefix does not depend on the continuation. -/
theorem fill_append (step : Nat → Nat → Finset Point → Finset Nat)
    (time : Nat) (P : Finset Point) (xs ys : List Nat) :
    fill step time P (xs ++ ys) =
      fill step (time + xs.length) (fill step time P xs) ys := by
  induction xs generalizing time P with
  | nil => simp [fill]
  | cons x xs ih =>
    simpa [fill, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (ih (time + 1) (P ∪ row time (step time x P)))

end RotationBST.Arboral
