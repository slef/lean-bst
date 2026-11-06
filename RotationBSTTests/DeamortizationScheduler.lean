module

public import RotationBST.Algorithms.Deamortization.Scheduler.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.DeamortizationScheduler
open Deamortization.Scheduler

private def leaf : Tree := .node .nil .nil
private def tree : Tree := .node leaf leaf
private def root : Pointer.Config := ⟨tree, []⟩
private def left : Pointer.Config := ⟨leaf, [.left leaf]⟩
private def right : Pointer.Config := ⟨leaf, [.right leaf]⟩
private def first : Request := ⟨0, [.downRight, .upRight, .downLeft]⟩
private def second : Request := ⟨1, [.upLeft]⟩
private def third : Request := ⟨2, [.downRight]⟩
private def requests : List Request := [first, second, third]

private theorem depths (x : Nat) (hx : x < tree.size) : Tree.depth tree x ≤ 1 := by
  change x < 3 at hx
  interval_cases x <;> decide

private theorem firstReady : Prepared 1 root first left := by
  refine ⟨rfl, ⟨3, left, by decide, rfl, rfl⟩, ?_⟩
  intro cut middle replay x hx
  have same : middle.tree = tree := by
    by_cases early : cut < 3
    · interval_cases cut <;>
        simp [first, root, tree, leaf, Multifinger.replay, Multifinger.perform] at replay <;>
        subst middle <;> rfl
    · have enough : first.instructions.length ≤ cut := by change 3 ≤ cut; omega
      rw [List.take_of_length_le enough] at replay
      have eq : middle = left := Option.some.inj (replay.symm.trans rfl)
      subst middle
      rfl
  rw [same] at hx ⊢
  exact depths x hx

private theorem secondReady : Prepared 1 left second root := by
  refine ⟨rfl, ⟨1, root, by decide, rfl, rfl⟩, ?_⟩
  intro cut middle replay x hx
  have same : middle.tree = tree := by
    cases cut <;> simp [second, left, leaf, Multifinger.replay, Multifinger.perform] at replay <;>
      subst middle <;> rfl
  rw [same] at hx ⊢
  exact depths x hx

private theorem thirdReady : Prepared 1 root third right := by
  refine ⟨rfl, ⟨1, right, by decide, rfl, rfl⟩, ?_⟩
  intro cut middle replay x hx
  have same : middle.tree = tree := by
    cases cut <;> simp [third, root, tree, leaf, Multifinger.replay, Multifinger.perform] at replay <;>
      subst middle <;> rfl
  rw [same] at hx ⊢
  exact depths x hx

private theorem prepared : PreparedStream 1 root requests right :=
  .cons firstReady (.cons secondReady (.cons thirdReady .nil))

-- Five original instructions are planned, but three unit-budget windows can
-- consume at most three. All requests are still served, and at least two
-- original operations remain queued at the exact continuing cursor.
example {p : Policy} (policyValid : PolicyValid 1 p) :
    ∃ out, run p (initial root) requests = some out ∧ Valid 1 out.state ∧
      out.state.planned = right ∧ 2 ≤ out.state.pending.length ∧ out.instructions.length ≤ 15 ∧
      Multifinger.replay out.instructions root = some out.state.cursor ∧
      Multifinger.Execution (cursorState root) [0, 1, 2] (cursorState out.state.cursor)
        (3 + out.instructions.length) ∧
      out.costs.length = 3 ∧ ∀ cost ∈ out.costs, cost ≤ 6 := by
  have valid : Valid 1 (initial root) := Results.initial_valid (by decide) depths
  obtain ⟨out, completed, planned, nextValid, replay, execution, account, work, count, _, costs, consumed⟩ :=
    Results.run_spec policyValid valid prepared
  change out.state.pending.length + out.consumed = 5 at account
  change out.consumed ≤ 3 at consumed
  exact ⟨out, completed, nextValid, planned, by omega, by omega, replay, execution, count, costs⟩

-- Extending the input retains the emitted prefix and its request charges,
-- even while work from earlier requests remains pending.
example (p : Policy) {out : Output} (completed : run p (initial root) requests = some out) :
    ∃ earlier, run p (initial root) [first, second] = some earlier ∧
      earlier.instructions <+: out.instructions ∧ earlier.costs <+: out.costs :=
  Results.run_prefix p (initial root) [first, second] [third] completed

-- A zero-operation request can be served without consuming original work;
-- the existing persistent finger and empty pending suffix are retained.
example {p : Policy} (policyValid : PolicyValid 1 p) :
    ∃ out, run p (initial left) [⟨0, []⟩] = some out ∧
      out.instructions = [] ∧ out.state.cursor = left ∧ out.state.pending = [] ∧ out.costs = [1] := by
  have valid : Valid 1 (initial left) := Results.initial_valid (by decide) depths
  have requestReady : Prepared 1 left ⟨0, []⟩ left := by
    refine ⟨rfl, ⟨0, left, le_rfl, rfl, rfl⟩, ?_⟩
    intro cut middle replay x hx
    simp only [List.take_nil, Multifinger.replay, Option.some.injEq] at replay
    subst middle
    exact depths x hx
  obtain ⟨out, completed, _, _, replay, _, account, work, count, total, _, _⟩ :=
    Results.run_spec policyValid valid (.cons requestReady .nil)
  change out.state.pending.length + out.consumed = 0 at account
  have empty : out.instructions = [] := List.length_eq_zero_iff.mp (by omega)
  have cursor : out.state.cursor = left := by
    simpa only [empty, Multifinger.replay, Option.some.injEq, initial] using replay.symm
  refine ⟨out, completed, empty, cursor, List.length_eq_zero_iff.mp (by omega), ?_⟩
  have singleton := List.length_eq_one_iff.mp count
  obtain ⟨cost, costs⟩ := singleton
  rw [costs, empty] at total
  simp only [List.sum_singleton, List.length_cons, List.length_nil] at total
  simpa only [total] using costs

end RotationBST.Tests.DeamortizationScheduler
