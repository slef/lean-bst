module

public import RotationBST.Algorithms.Combination.Rounds.Certificates.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboCertificates
open Combo
open Rounds.Certificates

private def worker : Controller.Worker Nat :=
  ⟨fun _ => 0, fun side state _ => if side then (0, true) else if state = 0 then (1, false) else (0, true)⟩
private def requests : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
private def start : Controller.State Nat := Controller.initial worker 3

private theorem execution : Controller.Execution worker 3 7 start requests ⟨true, 0, 0⟩ 33 3 :=
  .cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide)
    (.cons (by decide) (.cons (by decide) (.cons (by decide) (.cons (by decide) .nil)))))))

-- Three closed rounds are recorded. The retry request is included both at
-- the end of the old round and at the beginning of the new one.
example : records worker 3 7 start 0 0 [] requests =
    [⟨⟨false, 0, 2⟩, [0, 1]⟩, ⟨⟨true, 1, 5⟩, [1, 2, 3, 4]⟩, ⟨⟨false, 4, 6⟩, [4, 5]⟩] := by decide

example : Worker.ClosedRound worker true (worker.restart true) 3 [1, 2, 3, 4] :=
  Results.closed_spans execution ⟨true, 1, 5⟩ (by decide)
example : Worker.ClosedRound worker false (worker.restart false) 3 [4, 5] :=
  Results.closed_spans execution ⟨false, 4, 6⟩ (by decide)

private theorem fast_access (x : Nat) : Worker.Access worker true 0 x 0 1 := .done rfl
private theorem four_requests : Worker.Requests worker true 0 [1, 2, 3, 4] 0 4 :=
  .cons (fast_access 1) (.cons (fast_access 2) (.cons (fast_access 3) (.cons (fast_access 4) .nil)))

-- The budget comparison now applies to a later round, not only the first.
example : 3 < 4 := Results.span_lower_bound execution ⟨true, 1, 5⟩ (by decide) 0 4 four_requests

-- The final round uses its budget exactly but has not switched away yet;
-- it is correctly excluded from the exhausted-round certificates.
example : (⟨true, 5, 8⟩ : Rounds.Span) ∉ (Rounds.spans worker 3 7 start 0 requests).dropLast := by decide

-- Certificates also work with a completed prefix already carried in a round.
private theorem active : Active worker 3 ⟨false, 0, 1⟩ [9] :=
  ⟨2, .cons (.more rfl (.done rfl)) .nil, by decide⟩
private theorem continued : Controller.Execution worker 3 7 ⟨false, 0, 1⟩ [10] ⟨true, 0, 2⟩ 9 1 :=
  .cons (by decide) .nil
example : Worker.ClosedRound worker false (worker.restart false) 3 [9, 10] :=
  Results.records_closed continued 9 10 [9] active ⟨⟨false, 9, 11⟩, [9, 10]⟩ (by decide)

example : records worker 3 7 start 0 0 [] [] = [] := rfl

end RotationBST.Tests.ComboCertificates
