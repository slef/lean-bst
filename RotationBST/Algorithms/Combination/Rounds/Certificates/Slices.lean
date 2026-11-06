module

public import RotationBST.Algorithms.Combination.Rounds.Certificates.Spans
public import RotationBST.Algorithms.Combination.Rounds.Certificates.Propagation

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates

/-- Recorded request values are exactly their indicated contiguous slice,
including the failed last request. Offsets may begin in a larger sequence. -/
theorem records_slice {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) (aligned : start + earlier.length = offset) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      record.requests = ((earlier ++ xs).drop (record.span.start - start)).take (record.span.stop - record.span.start) := by
  induction xs generalizing s start offset earlier with
  | nil => simp [records]
  | cons x xs ih =>
    by_cases done : (Controller.serve worker budget restore s x).done = true
    · by_cases changed : (Controller.serve worker budget restore s x).switched = true
      · intro record member
        simp only [records, done, changed, ↓reduceIte, List.mem_cons] at member
        rcases member with rfl | member
        · dsimp only
          rw [Nat.sub_self, List.drop_zero]
          have length : offset + 1 - start = (earlier ++ [x]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          rw [length]
          simpa only [List.append_assoc, List.singleton_append] using
            (List.take_left (l₁ := earlier ++ [x]) (l₂ := xs)).symm
        · have child := ih (Controller.serve worker budget restore s x).state offset (offset + 1) [x] (by simp) record member
          have bound := (records_bounds worker budget restore
            (Controller.serve worker budget restore s x).state offset (offset + 1) [x] xs (by omega) record member).1
          have delta : record.span.start - start = earlier.length + (record.span.start - offset) := by omega
          rw [delta, ← List.drop_drop, List.drop_left]
          simpa only [List.singleton_append] using child
      · have alignment : start + (earlier ++ [x]).length = offset + 1 := by
          simp only [List.length_append, List.length_singleton]
          omega
        have rest := ih (Controller.serve worker budget restore s x).state start (offset + 1) (earlier ++ [x]) alignment
        simpa only [records, done, changed, Bool.false_eq_true, ↓reduceIte, List.append_assoc, List.singleton_append] using rest
    · simp [records, done]

/-- Every exhausted span in the complete controller run has a worker-round
certificate from that worker's fixed restart state on the exact input slice. -/
theorem closed_spans {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore (Controller.initial worker budget) xs final cost switches) :
    ∀ span ∈ (spans worker budget restore (Controller.initial worker budget) 0 xs).dropLast,
      Worker.ClosedRound worker span.side (worker.restart span.side) budget
        ((xs.drop span.start).take (span.stop - span.start)) := by
  intro span member
  have mapped : span ∈ (records worker budget restore (Controller.initial worker budget) 0 0 [] xs).map Record.span := by
    simpa only [records_spans, spans, Nat.zero_add] using member
  obtain ⟨record, inRecords, same⟩ := List.mem_map.mp mapped
  have closed := records_closed execution 0 0 [] (initial_active worker budget) record inRecords
  have values := records_slice worker budget restore (Controller.initial worker budget) 0 0 [] xs rfl record inRecords
  simp only [List.nil_append, Nat.sub_zero, same] at values
  simpa only [same, values] using closed

/-- The paper's completed-round budget lower bound now applies to every
exhausted span, rather than only the first switch. -/
theorem span_lower_bound {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore (Controller.initial worker budget) xs final cost switches)
    (span : Span) (member : span ∈ (spans worker budget restore (Controller.initial worker budget) 0 xs).dropLast)
    (endState : σ) (work : Nat)
    (complete : Worker.Requests worker span.side (worker.restart span.side)
      ((xs.drop span.start).take (span.stop - span.start)) endState work) : budget < work :=
  (closed_spans execution span member).lower_bound complete

end RotationBST.Combo.Rounds.Certificates
