module

public import RotationBST.Algorithms.Deamortization.Scheduler.Policy
public import RotationBST.Models.Multifinger.PointerTrace
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Deamortization.Scheduler

private theorem key_live {cursor : Pointer.Config} (live : cursor.focus ≠ .nil) :
    cursor.key? = some (cursor.key?.getD 0) := by
  cases focus : cursor.focus with
  | nil => exact False.elim (live focus)
  | node l r => simp [Pointer.Config.key?, focus]

theorem response_replay {budget : Nat} {s : State} {request : Request} {out : Response}
    (correct : Correct budget s request out) :
    Multifinger.replay out.instructions s.cursor = some out.state.cursor := by
  obtain ⟨_, _, _, _, _, _, before, _, after, _, _⟩ := correct
  simp only [Response.instructions, Multifinger.replay_append, before, Option.bind_some, after]

theorem response_account {budget : Nat} {s : State} {request : Request} {out : Response}
    (correct : Correct budget s request out) :
    out.state.pending.length + out.consumed = s.pending.length + request.instructions.length := by
  obtain ⟨_, _, _, length, pending, _, _, _, _, _, _⟩ := correct
  rw [pending, List.length_drop]
  simp only [List.length_append] at length ⊢
  omega

/-- The existing one-finger semantics records the actual target visit, keeping
its cursor between requests rather than silently resetting to the root. -/
theorem response_serves {budget : Nat} {s : State} {request : Request} {out : Response}
    (valid : Valid budget s) (correct : Correct budget s request out) :
    Multifinger.Serves (cursorState s.cursor) (cursorState out.state.cursor) request.target
      (1 + out.instructions.length) := by
  obtain ⟨nextValid, _, _, _, _, _, before, touched, after, _, _⟩ := correct
  obtain ⟨firstTouches, firstLength, first⟩ := Multifinger.pointer_trace
    (Multifinger.Replay.Results.physical before) (key_live valid.1) touched
  obtain ⟨lastTouches, lastLength, last⟩ := Multifinger.pointer_trace
    (Multifinger.Replay.Results.physical after) touched (key_live nextValid.1)
  refine ⟨⟨out.visited.tree, fun _ => request.target⟩, firstTouches, lastTouches, 0,
    first, rfl, last, ?_⟩
  simp only [Response.instructions, List.length_append, firstLength, lastLength]
  omega

/-- Every prepared sequence is served by the same fixed policy. Work left in
pending is retained explicitly, so consumed-work accounting telescopes exactly. -/
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
      (∀ cost ∈ out.costs, cost ≤ 1 + 5 * budget) ∧ out.consumed ≤ budget * requests.length := by
  induction requests generalizing s finish with
  | nil =>
    cases ready
    refine ⟨⟨s, [], 0, []⟩, rfl, rfl, valid, rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · exact .nil
    · simp
    · simp
    · simp
    · simp
  | cons request requests ih =>
    cases ready with
    | cons prepared remaining =>
      obtain ⟨first, firstEq, correct⟩ := policyValid s request valid ⟨_, prepared⟩
      have nextPlanned := Option.some.inj (correct.2.1.symm.trans prepared.1)
      rw [← nextPlanned] at remaining
      obtain ⟨last, lastEq, planned, lastValid, lastReplay, lastExecution, lastAccount,
        lastWork, lastCount, lastSum, lastCosts, lastConsumed⟩ := ih correct.1 remaining
      have firstReplay := response_replay correct
      have firstExecution := response_serves valid correct
      have firstAccount := response_account correct
      obtain ⟨_, _, firstConsumed, _, _, _, _, _, _, firstWork, firstCost⟩ := correct
      refine ⟨⟨last.state, first.instructions ++ last.instructions, first.consumed + last.consumed,
        (1 + first.instructions.length) :: last.costs⟩, ?_, planned, lastValid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [run, firstEq, Option.bind_some, lastEq, Option.map_some]
      · simpa only [Multifinger.replay_append, firstReplay, Option.bind_some] using lastReplay
      · convert Multifinger.Execution.cons firstExecution lastExecution using 1 <;>
          simp only [List.map_cons, List.length_cons, List.length_append]
        omega
      · simp only [List.map_cons, List.sum_cons]
        omega
      · simp only [List.length_append]
        omega
      · simp only [List.length_cons, lastCount]
      · simp only [List.sum_cons, lastSum, List.length_cons, List.length_append]
        omega
      · intro cost member
        rcases List.mem_cons.mp member with rfl | later
        · exact firstCost
        · exact lastCosts cost later
      · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
        omega

/-- The request costs refer to the actual segments of this very output stream,
not merely to some list with the same sum and length. -/
theorem run_served {budget : Nat} {p : Policy} (policyValid : PolicyValid budget p)
    {s : State} {requests : List Request} {finish : Pointer.Config} {out : Output}
    (valid : Valid budget s) (ready : PreparedStream budget s.planned requests finish)
    (completed : run p s requests = some out) :
    ServedStream s.cursor (requests.map Request.target) out.state.cursor out.instructions out.costs := by
  induction requests generalizing s finish out with
  | nil =>
    simp only [run, Option.some.injEq] at completed
    subst out
    exact .nil
  | cons request requests ih =>
    cases ready with
    | cons prepared remaining =>
      obtain ⟨first, firstEq, correct⟩ := policyValid s request valid ⟨_, prepared⟩
      have nextPlanned := Option.some.inj (correct.2.1.symm.trans prepared.1)
      rw [← nextPlanned] at remaining
      cases lastEq : run p first.state requests with
      | none => simp only [run, firstEq, Option.bind_some, lastEq, Option.map_none, reduceCtorEq] at completed
      | some last =>
        have rest := ih correct.1 remaining lastEq
        simp only [run, firstEq, Option.bind_some, lastEq, Option.map_some, Option.some.injEq] at completed
        subst out
        obtain ⟨_, _, _, _, _, _, before, touched, after, _, _⟩ := correct
        exact ServedStream.cons before touched after rest

/-- Exact code and charge-list composition makes the scheduler causal in its
sequence of prepared requests, with no dependence on later input. -/
theorem run_append (p : Policy) (s : State) (xs ys : List Request) :
    run p s (xs ++ ys) = (run p s xs).bind fun first =>
      (run p first.state ys).map fun last =>
        ⟨last.state, first.instructions ++ last.instructions,
          first.consumed + last.consumed, first.costs ++ last.costs⟩ := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons request requests ih =>
    simp only [List.cons_append, run]
    cases firstEq : p s request with
    | none => rfl
    | some first =>
      simp only [Option.bind_some, ih]
      cases middleEq : run p first.state requests with
      | none => rfl
      | some middle =>
        simp only [Option.bind_some, Option.map_some]
        cases lastEq : run p middle.state ys <;> simp [List.append_assoc, Nat.add_assoc]

theorem run_prefix (p : Policy) (s : State) (xs ys : List Request) {out : Output}
    (completed : run p s (xs ++ ys) = some out) :
    ∃ first, run p s xs = some first ∧ first.instructions <+: out.instructions ∧ first.costs <+: out.costs := by
  rw [run_append] at completed
  cases firstEq : run p s xs with
  | none => simp [firstEq] at completed
  | some first =>
    simp only [firstEq, Option.bind_some] at completed
    cases lastEq : run p first.state ys with
    | none => simp [lastEq] at completed
    | some last =>
      simp only [lastEq, Option.map_some, Option.some.injEq] at completed
      subst out
      exact ⟨first, rfl, ⟨last.instructions, rfl⟩, ⟨last.costs, rfl⟩⟩

end RotationBST.Deamortization.Scheduler
