module

public import RotationBST.Algorithms.Combination.Rounds.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboRounds
open Combo

private def worker : Controller.Worker Nat :=
  ⟨fun _ => 0, fun side state _ => if side then (0, true) else if state = 0 then (1, false) else (0, true)⟩
private def requests : List Nat := [0, 0, 0, 0, 0]
private def start : Controller.State Nat := Controller.initial worker 3

-- Equal keys still have distinct request indices. Interruptions occur at the
-- second and fifth requests, even when the prefix has a nonzero offset.
example : Rounds.cuts worker 3 7 start 10 requests = [11, 14] := by decide

private theorem coverage : Rounds.spans worker 3 7 start 10 requests =
    [⟨false, 10, 12⟩, ⟨true, 11, 15⟩, ⟨false, 14, 15⟩] := by decide

example : Rounds.Separated (Rounds.spans worker 3 7 start 10 requests) :=
  Rounds.Results.spans_separated worker 3 7 start 10 requests

example : Rounds.count false (Rounds.spans worker 3 7 start 10 requests) = 2 := by decide
example : Rounds.count true (Rounds.spans worker 3 7 start 10 requests) = 1 := by decide

-- Overlap is allowed between opposite workers, never counted twice for one.
example : Rounds.charge false (fun _ => 1) (Rounds.spans worker 3 7 start 10 requests) = 3 := by
  rw [coverage]
  norm_num [Rounds.charge, Rounds.Span.charge]
example : Rounds.charge true (fun _ => 1) (Rounds.spans worker 3 7 start 10 requests) = 4 := by
  rw [coverage]
  norm_num [Rounds.charge, Rounds.Span.charge]

example (selected : Bool) (weights : Nat → ℝ) (nonneg : ∀ i, 0 ≤ weights i) :
    Rounds.charge selected weights (Rounds.spans worker 3 7 start 10 requests) ≤
      ∑ i ∈ Finset.Ico 10 (10 + requests.length), weights i :=
  Rounds.Results.charge_le_interval worker 3 7 start 10 requests selected weights nonneg

example {final : Controller.State Nat} {cost switches : Nat}
    (execution : Controller.Execution worker 3 7 start requests final cost switches) :
    cost ≤ (2 * Rounds.count true (Rounds.spans worker 3 7 start 10 requests) + 1) * 10 :=
  Rounds.Results.work_by_rounds execution (by decide) 10 true

-- A zero-work old attempt at the start of a request is covered conservatively
-- by the closing round, while still remaining disjoint from later same-side rounds.
example : Rounds.spans worker 2 7 (Controller.initial worker 2) 0 [0, 0] =
    [⟨false, 0, 2⟩, ⟨true, 1, 2⟩] := by decide

-- The empty prefix has its initial empty round and zero charge.
example : Rounds.spans worker 3 7 start 10 [] = [⟨false, 10, 10⟩] := by decide
example : Rounds.charge false (fun _ => 1) (Rounds.spans worker 3 7 start 10 []) = 0 := by
  norm_num [Rounds.charge, Rounds.Span.charge, Rounds.spans, Rounds.cuts, Rounds.partition, start, Controller.initial]

end RotationBST.Tests.ComboRounds
