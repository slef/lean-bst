module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Rounds.Certificates.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Rounds.Certificates.Results

theorem records_closed {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches)
    (start offset : Nat) (earlier : List Nat) (active : Active worker budget s earlier) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      Worker.ClosedRound worker record.span.side (worker.restart record.span.side) budget record.requests :=
  RotationBST.Combo.Rounds.Certificates.records_closed execution start offset earlier active

theorem initial_active {σ : Type} (worker : Controller.Worker σ) (budget : Nat) :
    Active worker budget (Controller.initial worker budget) [] :=
  RotationBST.Combo.Rounds.Certificates.initial_active worker budget

theorem records_spans {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) :
    (records worker budget restore s start offset earlier xs).map Record.span =
      (partition s.side start (offset + xs.length) (cuts worker budget restore s offset xs)).dropLast :=
  RotationBST.Combo.Rounds.Certificates.records_spans worker budget restore s start offset earlier xs

theorem records_bounds {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) (before : start ≤ offset) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      start ≤ record.span.start ∧ record.span.start ≤ record.span.stop ∧ record.span.stop ≤ offset + xs.length :=
  RotationBST.Combo.Rounds.Certificates.records_bounds worker budget restore s start offset earlier xs before

theorem records_slice {σ : Type} (worker : Controller.Worker σ) (budget restore : Nat)
    (s : Controller.State σ) (start offset : Nat) (earlier xs : List Nat) (aligned : start + earlier.length = offset) :
    ∀ record ∈ records worker budget restore s start offset earlier xs,
      record.requests = ((earlier ++ xs).drop (record.span.start - start)).take (record.span.stop - record.span.start) :=
  RotationBST.Combo.Rounds.Certificates.records_slice worker budget restore s start offset earlier xs aligned

theorem closed_spans {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore (Controller.initial worker budget) xs final cost switches) :
    ∀ span ∈ (spans worker budget restore (Controller.initial worker budget) 0 xs).dropLast,
      Worker.ClosedRound worker span.side (worker.restart span.side) budget
        ((xs.drop span.start).take (span.stop - span.start)) :=
  RotationBST.Combo.Rounds.Certificates.closed_spans execution

theorem span_lower_bound {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {final : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore (Controller.initial worker budget) xs final cost switches)
    (span : Span) (member : span ∈ (spans worker budget restore (Controller.initial worker budget) 0 xs).dropLast)
    (endState : σ) (work : Nat)
    (complete : Worker.Requests worker span.side (worker.restart span.side)
      ((xs.drop span.start).take (span.stop - span.start)) endState work) : budget < work :=
  RotationBST.Combo.Rounds.Certificates.span_lower_bound execution span member endState work complete

theorem records_tail_closed {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches)
    (start offset : Nat) (earlier : List Nat) :
    ∀ record ∈ (records worker budget restore s start offset earlier xs).tail,
      Worker.ClosedRound worker record.span.side (worker.restart record.span.side) budget record.requests :=
  RotationBST.Combo.Rounds.Certificates.records_tail_closed execution start offset earlier

theorem interior_spans {σ : Type} {worker : Controller.Worker σ} {budget restore : Nat}
    {s t : Controller.State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Controller.Execution worker budget restore s xs t cost switches) :
    ∀ span ∈ (spans worker budget restore s 0 xs).dropLast.tail,
      Worker.ClosedRound worker span.side (worker.restart span.side) budget
        ((xs.drop span.start).take (span.stop - span.start)) :=
  RotationBST.Combo.Rounds.Certificates.interior_spans execution

end RotationBST.Combo.Rounds.Certificates.Results

/-- info: abstract audit passed for `RotationBST.Combo.Rounds.Certificates.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Rounds.Certificates.Results allowing [
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Certificates.Definitions.Abstract]
