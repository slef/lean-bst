module

public import RotationBST.Algorithms.Combination.Rounds.Certificates.Slices

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates

/-- A window may start partway through a worker round. After its first switch,
every closed round again has a certificate from the fixed restart state. -/
theorem records_tail_closed {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches)
    (start offset : Nat) (earlier : List Nat) :
    ∀ record ∈ (records worker budget restore s start offset earlier xs).tail,
      Worker.ClosedRound worker record.span.side (worker.restart record.span.side) budget record.requests := by
  induction execution generalizing start offset earlier with
  | nil => simp [records]
  | @cons s t x xs cost switches done tail ih =>
    by_cases changed : (Controller.serve worker budget restore s x).switched = true
    · have firstDone : (Controller.attempt worker s.side x s.left s.workerState).done ≠ true := by
        intro firstDone
        simp only [Controller.serve, firstDone, ↓reduceIte, Bool.false_eq_true] at changed
      let second := Controller.attempt worker (!s.side) x budget (worker.restart (!s.side))
      have next : Controller.serve worker budget restore s x =
          ⟨⟨!s.side, second.state, second.left⟩, second.done, true,
            s.left - (Controller.attempt worker s.side x s.left s.workerState).left + restore + (budget - second.left)⟩ := by
        simpa only [Controller.serve] using ite_eq_right firstDone
      have secondRun := Controller.attempt_run worker (!s.side) x budget (worker.restart (!s.side))
      have secondDone : second.done = true := by simpa only [next] using done
      have active : Active worker budget (Controller.serve worker budget restore s x).state [x] := by
        refine ⟨budget - second.left, ?_, ?_⟩
        · simpa only [next, Nat.add_zero] using Worker.Requests.cons (secondRun.to_access secondDone) Worker.Requests.nil
        · simpa only [next] using secondRun.account
      simpa only [records, done, changed, ↓reduceIte, List.tail_cons] using
        records_closed tail offset (offset + 1) [x] active
    · simpa only [records, done, changed, Bool.false_eq_true, ↓reduceIte] using
        ih start (offset + 1) (earlier ++ [x])

/-- Excluding the two boundary rounds leaves closed spans whose complete
request slices started at the worker's fixed restart state, even for an
arbitrary initial controller state. -/
theorem interior_spans {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) :
    ∀ span ∈ (spans worker budget restore s 0 xs).dropLast.tail,
      Worker.ClosedRound worker span.side (worker.restart span.side) budget
        ((xs.drop span.start).take (span.stop - span.start)) := by
  intro span member
  have mapped : span ∈ ((records worker budget restore s 0 0 [] xs).tail).map Record.span := by
    simpa only [List.map_tail, records_spans, spans, Nat.zero_add] using member
  obtain ⟨record, inRecords, same⟩ := List.mem_map.mp mapped
  have closed := records_tail_closed execution 0 0 [] record inRecords
  have values := records_slice worker budget restore s 0 0 [] xs rfl record
    (List.mem_of_mem_tail inRecords)
  simp only [List.nil_append, Nat.sub_zero, same] at values
  simpa only [same, values] using closed

end RotationBST.Combo.Rounds.Certificates
