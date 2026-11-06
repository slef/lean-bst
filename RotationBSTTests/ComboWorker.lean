module

public import RotationBST.Algorithms.Combination.Worker.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboWorker
open Combo

private def worker : Controller.Worker Nat :=
  ⟨fun _ => 0, fun side state _ => if side then (0, true) else if state = 0 then (1, false) else (0, true)⟩

private theorem access (x : Nat) : Worker.Access worker false 0 x 0 2 :=
  .more rfl (.done rfl)

private theorem two_requests (x y : Nat) : Worker.Requests worker false 0 [x, y] 0 4 :=
  .cons (access x) (.cons (access y) .nil)

-- Closing a round midway through the second request consumes three units;
-- actually completing its two-request span on worker 0 takes four.
private theorem cut : Rounds.cuts worker 3 7 (Controller.initial worker 3) 8 [0, 1] = [9] := by decide
example : Worker.ClosedRound worker false 0 3 [0, 1] :=
  Worker.Results.first_closed worker 3 7 (Controller.initial worker 3) 8 [0, 1] 9 [] cut
example : (Controller.initial worker 3).left < 4 :=
  Worker.Results.first_lower_bound worker 3 7 (Controller.initial worker 3) 8 [0, 1] 9 [] cut 0 4 (two_requests 0 1)

-- Completed work before an interruption is reattached to the same initial
-- worker state, with its cost added back into the full round budget.
example (x y : Nat) : Worker.ClosedRound worker false 0 3 [x, y] := by
  have prefixRun : Worker.Requests worker false 0 [x] 0 2 := .cons (access x) .nil
  have remaining : Worker.ClosedRound worker false 0 1 [y] :=
    .failed (.more rfl .exhausted) rfl
  exact Worker.Results.ClosedRound.prepend prefixRun remaining

-- A zero-budget attempt still fails before the first positive-cost request
-- step; this covers a round that finished its previous request at the limit.
example (x : Nat) : Worker.ClosedRound worker false 0 0 [x] := .failed .exhausted rfl
example : Worker.ClosedRound worker false 0 2 [0, 1] :=
  Worker.Results.first_closed worker 2 7 (Controller.initial worker 2) 0 [0, 1] 1 [] (by decide)

-- Extra unused budget changes neither the completed state nor consumed work.
example : (0 : Nat) = 0 ∧ (2 : Nat) = 2 :=
  Worker.Results.completed_unique
    (Controller.AttemptRun.more (fuel := 2) rfl (.done (fuel := 1) rfl) :
      Controller.AttemptRun worker false 0 3 0 ⟨0, 1, true⟩ 2) rfl
    (Controller.AttemptRun.more (fuel := 5) rfl (.done (fuel := 4) rfl) :
      Controller.AttemptRun worker false 0 6 0 ⟨0, 4, true⟩ 2) rfl

example (final : Nat) (cost : Nat) (run : Worker.Requests worker false 0 [0, 1] final cost) :
    final = 0 ∧ cost = 4 := Worker.Results.Requests.unique run (two_requests 0 1)

end RotationBST.Tests.ComboWorker
