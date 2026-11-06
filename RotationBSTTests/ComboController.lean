module

public import RotationBST.Algorithms.Combination.Controller.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboController
open Combo.Controller

/-- Worker 0 needs two units per request; worker 1 needs one. The state is
partial progress on the current request, cleared on completion and restart. -/
private def worker : Worker Nat :=
  ⟨fun _ => 0, fun side state _ => if side then (0, true) else if state = 0 then (1, false) else (0, true)⟩

private theorem bounded (n : Nat) : FreshBound worker n 2 := by
  intro side x _
  cases side <;> rfl

-- One unused unit cannot finish worker 0's next request. Its partial attempt
-- is charged, then exactly one restore and a retry on worker 1 are charged.
example : serve worker 3 7 ⟨false, 0, 1⟩ 4 = ⟨⟨true, 0, 2⟩, true, true, 9⟩ := by decide

-- Finishing exactly at the budget boundary succeeds. The following request
-- switches before doing any more worker-0 steps.
example : serve worker 2 7 (initial worker 2) 0 = ⟨⟨false, 0, 0⟩, true, false, 2⟩ := by decide
example : serve worker 2 7 ⟨false, 0, 0⟩ 1 = ⟨⟨true, 0, 1⟩, true, true, 8⟩ := by decide

-- Two switches alternate the workers, with the current request retried only
-- after a switch. The five-request trace has total charged work 22.
example : run worker 3 7 (initial worker 3) [0, 1, 2, 3, 4] = some (⟨false, 0, 1⟩, 22) := by decide

example : ∃ final cost switches, Combo.Controller.Execution worker 3 7 (initial worker 3) [0, 1, 2, 3, 4] final cost switches ∧
    run worker 3 7 (initial worker 3) [0, 1, 2, 3, 4] = some (final, cost) ∧ final.left ≤ 3 ∧
    cost ≤ (2 * 3 + 7) * [0, 1, 2, 3, 4].length :=
  Results.complete worker 5 2 3 7 (bounded 5) (by decide) (initial worker 3) (by decide)
    [0, 1, 2, 3, 4] (by intro x member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)

example {final : State Nat} {cost switches : Nat}
    (execution : Combo.Controller.Execution worker 3 7 (initial worker 3) [0, 1, 2, 3, 4] final cost switches) :
    cost + final.left = 3 + switches * 10 := Results.Execution.account execution

example : (serve worker 3 7 ⟨true, worker.restart true, 3⟩ 4).switched = false ∧
    (serve worker 3 7 ⟨true, worker.restart true, 3⟩ 4).work ≤ 2 :=
  Results.fresh_completes worker 5 2 3 7 (bounded 5) (by decide) true 4 (by decide)

private def stuck : Worker Nat := ⟨fun _ => 0, fun _ state _ => (state + 1, false)⟩

-- Without the fresh bound the function reports failure, rather than claiming
-- that an exhausted second attempt has served the request.
example : (serve stuck 3 7 (initial stuck 3) 0).done = false := by decide
example : run stuck 3 7 (initial stuck 3) [0] = none := by decide

end RotationBST.Tests.ComboController
