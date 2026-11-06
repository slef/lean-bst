module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Scheduler.AbstractBridge

@[expose] public section
namespace RotationBST.Deamortization.Scheduler.Results

theorem initial_valid {budget : Nat} {cursor : Pointer.Config} (live : cursor.focus ≠ .nil)
    (depths : ∀ x < cursor.tree.size, Tree.depth cursor.tree x ≤ budget) :
    Valid budget (initial cursor) :=
  RotationBST.Deamortization.Scheduler.initial_valid live depths

theorem policy_exists (budget : Nat) : ∃ p : Policy, PolicyValid budget p :=
  RotationBST.Deamortization.Scheduler.policy_exists budget

theorem response_replay {budget : Nat} {s : State} {request : Request} {out : Response}
    (correct : Correct budget s request out) :
    Multifinger.replay out.instructions s.cursor = some out.state.cursor :=
  RotationBST.Deamortization.Scheduler.response_replay correct

theorem response_account {budget : Nat} {s : State} {request : Request} {out : Response}
    (correct : Correct budget s request out) :
    out.state.pending.length + out.consumed = s.pending.length + request.instructions.length :=
  RotationBST.Deamortization.Scheduler.response_account correct

theorem response_serves {budget : Nat} {s : State} {request : Request} {out : Response}
    (valid : Valid budget s) (correct : Correct budget s request out) :
    Multifinger.Serves (cursorState s.cursor) (cursorState out.state.cursor) request.target
      (1 + out.instructions.length) :=
  RotationBST.Deamortization.Scheduler.response_serves valid correct

theorem run_spec {budget : Nat} {p : Policy} (policyValid : PolicyValid budget p)
    {s : State} {requests : List Request} {finish : Pointer.Config}
    (valid : Valid budget s) (ready : PreparedStream budget s.planned requests finish) :
    ∃ out, run p s requests = some out ∧ out.state.planned = finish ∧ Valid budget out.state ∧
      Multifinger.replay out.instructions s.cursor = some out.state.cursor ∧
      Multifinger.Execution (cursorState s.cursor) (requests.map Request.target)
        (cursorState out.state.cursor) (requests.length + out.instructions.length) ∧
      out.state.pending.length + out.consumed =
        s.pending.length + (requests.map (fun request => request.instructions.length)).sum ∧
      out.instructions.length ≤ 5 * out.consumed ∧
      out.costs.length = requests.length ∧ out.costs.sum = requests.length + out.instructions.length ∧
      (∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget) ∧ out.consumed ≤ budget * requests.length :=
  RotationBST.Deamortization.Scheduler.run_spec policyValid valid ready

theorem run_append (p : Policy) (s : State) (xs ys : List Request) :
    run p s (xs ++ ys) = (run p s xs).bind fun first =>
      (run p first.state ys).map fun last =>
        ⟨last.state, first.instructions ++ last.instructions,
          first.consumed + last.consumed, first.costs ++ last.costs⟩ :=
  RotationBST.Deamortization.Scheduler.run_append p s xs ys

theorem run_prefix (p : Policy) (s : State) (xs ys : List Request) {out : Output}
    (completed : run p s (xs ++ ys) = some out) :
    ∃ first, run p s xs = some first ∧ first.instructions <+: out.instructions ∧ first.costs <+: out.costs :=
  RotationBST.Deamortization.Scheduler.run_prefix p s xs ys completed

theorem run_served {budget : Nat} {p : Policy} (policyValid : PolicyValid budget p)
    {s : State} {requests : List Request} {finish : Pointer.Config} {out : Output}
    (valid : Valid budget s) (ready : PreparedStream budget s.planned requests finish)
    (completed : run p s requests = some out) :
    ServedStream s.cursor (requests.map Request.target) out.state.cursor out.instructions out.costs :=
  RotationBST.Deamortization.Scheduler.run_served policyValid valid ready completed

end RotationBST.Deamortization.Scheduler.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Scheduler.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Scheduler.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract]
