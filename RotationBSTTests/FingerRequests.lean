module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Abstract
public import RotationBST.Algorithms.Deamortization.Finger.Abstract
public import RotationBST.Algorithms.Deamortization.Weighted.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerRequests
open HeavyPath HeavyPath.Finger.History HeavyPath.Finger.History.Simulation LabelledCursor

private def leaf (key : Nat) : LabelledTree Nat := .node .nil key .nil
private def source : Config Nat := ⟨.node (leaf 1) 2 (leaf 3), []⟩
private def weights (x : Nat) : ℝ := (x : ℝ) + 1
private def roundtrip : List Multifinger.Opcode :=
  [.downLeft, .upLeft, .downRight, .upRight, .downLeft,
    .rotateLeftChild, .downRight, .rotateRightChild]

private theorem positive : Positive weights source.tree := by
  norm_num [source, leaf, Config.tree, plug, Positive, weights]

-- The first downward move visits rank zero; all later work, including both
-- rotations, belongs to the same request and must remain in the output.
private theorem leftSearch : Requests.Serves source roundtrip 0 source :=
  ⟨[.downLeft], [.upLeft, .downRight, .upRight, .downLeft, .rotateLeftChild,
    .downRight, .rotateRightChild], ⟨leaf 1, [.left 2 (leaf 3)]⟩, rfl, rfl, rfl, rfl⟩

-- A request may already be satisfied before its first source instruction.
example : Requests.Serves source roundtrip 1 source :=
  ⟨[], roundtrip, source, rfl, rfl, rfl, rfl⟩

-- A visit at the very end is allowed as well.
example : Requests.Serves source [.downRight] 2 ⟨leaf 3, [.right (leaf 1) 2]⟩ :=
  ⟨[.downRight], [], ⟨leaf 3, [.right (leaf 1) 2]⟩, rfl, rfl, rfl, rfl⟩

private theorem rootSearch : Requests.Serves source [] 1 source :=
  ⟨[], [], source, rfl, rfl, rfl, rfl⟩

-- A total source algorithm: use a scripted mixed-operation search at this
-- source cursor and ordinary navigation everywhere else.
private noncomputable def fallback : Requests.Algorithm Nat :=
  Classical.choice (Requests.Results.algorithm_exists Nat)

private noncomputable def scripted : Requests.Algorithm Nat where
  step := fun past c key =>
    if c = source ∧ key = 0 then (roundtrip, source)
    else if c = source ∧ key = 1 then ([], source)
    else fallback.step past c key
  correct := by
    intro past c key nonempty validKey
    by_cases first : c = source ∧ key = 0
    · simp only [first]
      rcases first with ⟨rfl, rfl⟩
      exact leftSearch
    · simp only [first, ↓reduceIte]
      by_cases second : c = source ∧ key = 1
      · simp only [second]
        rcases second with ⟨rfl, rfl⟩
        exact rootSearch
      · simp only [second, ↓reduceIte]
        exact fallback.correct past c key nonempty validKey

-- Three requests include a repeated key and a zero-movement root request.
-- The original-tree Pointer.Execution includes startup and preserves the
-- nonuniform-weight depth certificate in its final state.
example : ∃ (p : Policy Nat) (start : State Nat) (startupCost : Nat) (out : Output Nat),
    PolicyValid weights p ∧
    Requests.run p scripted [] source start [0, 1, 0] = some out ∧
    out.source = source ∧
    Pointer.Execution source.tree.erase [0, 1, 0] out.state.pair.tree
      (startupCost + (3 + out.cost)) ∧
    startupCost + 3 + out.cost + out.state.potential ≤ 1295 ∧
    ∀ rank : Fin source.tree.inorder.length,
      (Tree.depth out.state.pair.tree rank.val : ℝ) ≤
        15 + 15 * Real.logb 2 (HeavyPath.mass weights source.tree /
          weights (source.tree.inorder[rank.val]'rank.isLt)) := by
  obtain ⟨p, policyValid⟩ := Simulation.Results.policy_exists weights
  obtain ⟨start, startupCost, _, _, _, execute⟩ :=
    Requests.Results.initialized_run policyValid scripted positive
  obtain ⟨out, completed, sourceEq, preserved, _, original, bound⟩ :=
    execute [] [0, 1, 0] (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have finalSource : (scripted.runFrom [] source [0, 1, 0]).2 = source := rfl
  have work : (scripted.runFrom [] source [0, 1, 0]).1.length = 16 := rfl
  change out.source = (scripted.runFrom [] source [0, 1, 0]).2 at sourceEq
  change startupCost + 3 + out.cost + out.state.potential ≤
    39 * 3 + 62 * (3 + (scripted.runFrom [] source [0, 1, 0]).1.length) at bound
  rw [finalSource] at sourceEq
  refine ⟨p, start, startupCost, out, policyValid, completed, sourceEq, original (by simp), ?_, ?_⟩
  · rw [work] at bound
    exact bound
  · intro rank
    have valid : ConfigValid weights source out.state := by simpa only [sourceEq] using preserved
    exact Simulation.Results.depth valid rank

-- Repeated visits to the current root require no physical instruction at all,
-- but Pointer.Execution still charges the three requests.
example {p : Policy Nat} (policyValid : PolicyValid weights p) {start : State Nat}
    (valid : ConfigValid weights source start) :
    Requests.run p scripted [] source start [1, 1, 1] = some ⟨source, start, []⟩ ∧
    Pointer.Execution start.pair.tree [1, 1, 1] start.pair.tree 3 := by
  have computed : Requests.run p scripted [] source start [1, 1, 1] = some ⟨source, start, []⟩ := rfl
  obtain ⟨out, completed, _, _, _, executed, _⟩ := Requests.Results.run_spec policyValid scripted [] valid
    [1, 1, 1] (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have eq : out = ⟨source, start, []⟩ := Option.some.inj (completed.symm.trans computed)
  subst out
  exact ⟨computed, executed⟩

-- Extending the requests preserves the literal physical output prefix.
example {p : Policy Nat} {start : State Nat} {out : Output Nat}
    (completed : Requests.run p scripted [] source start [0, 1, 0] = some out) :
    ∃ first, Requests.run p scripted [] source start [0] = some first ∧
      first.instructions <+: out.instructions :=
  Requests.Results.run_prefix p scripted [] source start [0] [1, 0] completed

-- The complete scheduler transforms the actual source algorithm, including
-- post-visit rotations and a zero-operation middle request. Both policies and
-- the initialized representation are chosen before all request sequences.
example : ∃ (sourcePolicy : Policy Nat) (scheduler : Deamortization.Scheduler.Policy)
    (start : State Nat) (startup : Nat) (out : Deamortization.Scheduler.Output),
    Pointer.Trace ⟨source.tree.erase, []⟩ ⟨start.pair.tree, []⟩ startup ∧ startup ≤ 48 ∧
    Deamortization.Finger.transform sourcePolicy scheduler scripted [] source start [0, 1, 0] = some out ∧
    Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some out.state.cursor ∧
    Multifinger.Execution (Deamortization.Scheduler.cursorState ⟨start.pair.tree, []⟩)
      [0, 1, 0] (Deamortization.Scheduler.cursorState out.state.cursor) (3 + out.instructions.length) ∧
    startup + 3 + out.instructions.length ≤ 5356 ∧ out.costs.length = 3 ∧
    out.costs.sum = 3 + out.instructions.length ∧
    ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 3 := by
  obtain ⟨sourcePolicy, scheduler, _, start, startup, _, _, _, trace, startupBound, _, execute⟩ :=
    Deamortization.Finger.Results.initialized_transform scripted source (by decide)
  obtain ⟨out, completed, replay, execution, total, count, sum, costs⟩ :=
    execute [] [0, 1, 0] (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have sourceWork : (scripted.runFrom [] source [0, 1, 0]).1.length = 16 := rfl
  change startup + 3 + out.instructions.length ≤ 131 * 3 + 3 +
    310 * (scripted.runFrom [] source [0, 1, 0]).1.length at total
  rw [sourceWork] at total
  refine ⟨sourcePolicy, scheduler, start, startup, out, trace, startupBound, completed,
    replay, execution, total, count, sum, ?_⟩
  intro cost member
  have bound := costs cost member
  change (cost : ℝ) < 251 + 195 * Real.logb 2 (3 : Nat) at bound
  norm_num only [Nat.cast_ofNat] at bound
  exact bound

-- Prefix causality is for user requests, not just prepared opcode lists.
example (sourcePolicy : Policy Nat) (scheduler : Deamortization.Scheduler.Policy)
    (start : State Nat) {out : Deamortization.Scheduler.Output}
    (completed : Deamortization.Finger.transform sourcePolicy scheduler scripted [] source start [0, 1, 0] = some out) :
    ∃ first, Deamortization.Finger.transform sourcePolicy scheduler scripted [] source start [0] = some first ∧
      first.instructions <+: out.instructions ∧ first.costs <+: out.costs :=
  Deamortization.Finger.Results.transform_prefix sourcePolicy scheduler scripted [] source start [0] [1, 0] completed

-- Minimum initialization removes additive credit from the actual movement
-- bound, while preserving visits, rotations, and the worst-case request bound.
example : ∃ (start : State Nat) (out : Deamortization.Scheduler.Output),
    Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some out.state.cursor ∧
    Deamortization.Scheduler.ServedStream ⟨start.pair.tree, []⟩ [0, 1, 0]
      out.state.cursor out.instructions out.costs ∧
    Multifinger.Execution (Deamortization.Scheduler.cursorState ⟨start.pair.tree, []⟩)
      [0, 1, 0] (Deamortization.Scheduler.cursorState out.state.cursor) (3 + out.instructions.length) ∧
    out.instructions.length ≤ 19840 ∧ out.costs.sum ≤ 19843 ∧
    ∀ cost ∈ out.costs, (cost : ℝ) < 251 + 195 * Real.logb 2 3 := by
  obtain ⟨_, _, _, start, _, _, _, _, _, _, _, _, execute⟩ :=
    Deamortization.Finger.Results.minimized_transform source (by decide)
  obtain ⟨out, _, replay, served, execution, work, _, total, costs⟩ := execute scripted [] [0, 1, 0]
    (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have sourceWork : (scripted.runFrom [] source [0, 1, 0]).1.length = 16 := rfl
  rw [sourceWork] at work
  refine ⟨start, out, replay, served, execution, work, ?_, ?_⟩
  · change out.costs.sum = 3 + out.instructions.length at total
    omega
  · intro cost member
    have bound := costs cost member
    change (cost : ℝ) < 251 + 195 * Real.logb 2 (3 : Nat) at bound
    norm_num only [Nat.cast_ofNat] at bound
    exact bound

-- The paper-level witness is one program for all inputs. Repeated accesses
-- at the current source root have zero source operations and therefore zero
-- physical operations, with no additive tree-size allowance. The same program
-- retains literal output prefixes on every successful extension.
example : ∃ (start : State Nat) (program : List Nat → Option Deamortization.Scheduler.Output)
    (out : Deamortization.Scheduler.Output),
    program [1, 1, 1] = some out ∧ out.instructions = [] ∧ out.costs.sum = 3 ∧
    Multifinger.Execution (Deamortization.Scheduler.cursorState ⟨start.pair.tree, []⟩)
      [1, 1, 1] (Deamortization.Scheduler.cursorState out.state.cursor) 3 ∧
    ∀ xs ys final, program (xs ++ ys) = some final →
      ∃ first, program xs = some first ∧ first.instructions <+: final.instructions ∧
        first.costs <+: final.costs := by
  obtain ⟨start, _, program, _, _, _, execute, online⟩ :=
    Deamortization.Finger.Results.deamortize (fun _ => scripted) source (by decide)
  obtain ⟨out, completed, _, _, execution, work, _, total, _⟩ := execute [1, 1, 1]
    (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have sourceWork : (scripted.runFrom [] source [1, 1, 1]).1.length = 0 := rfl
  rw [sourceWork] at work
  have empty : out.instructions = [] := List.length_eq_zero_iff.mp (by omega)
  refine ⟨start, program, out, completed, empty, ?_, ?_, online ⟨scripted, fun _ => rfl⟩⟩
  · simpa [empty] using total
  · simpa [empty] using execution

-- Offline strategies may depend on a future request count. The same theorem
-- still supplies a fixed initial representation and the pure comparison.
example : ∃ (start : State Nat) (program : List Nat → Option Deamortization.Scheduler.Output),
    ∀ keys, (∀ x ∈ keys, x < 3) → ∃ out, program keys = some out ∧
      Multifinger.Execution (Deamortization.Scheduler.cursorState ⟨start.pair.tree, []⟩) keys
        (Deamortization.Scheduler.cursorState out.state.cursor) (keys.length + out.instructions.length) ∧
      out.instructions.length ≤ 1240 *
        ((if keys.length % 2 = 0 then scripted else fallback).runFrom [] source keys).1.length := by
  obtain ⟨start, _, program, _, _, _, execute, _⟩ :=
    Deamortization.Finger.Results.deamortize
      (fun keys => if keys.length % 2 = 0 then scripted else fallback) source (by decide)
  refine ⟨start, program, ?_⟩
  intro keys validKeys
  obtain ⟨out, completed, _, _, execution, work, _, _, _⟩ := execute keys validKeys
  exact ⟨out, completed, execution, work⟩

-- One weighted transformation handles every request stream. The mixed stream
-- exercises all six source operations, including post-visit work; the same
-- program also serves three root requests with no physical instructions.
example : ∃ (program : List Nat → Option (Output Nat)) (start : State Nat) (out : Output Nat),
    program [0, 1, 0] = some out ∧
    Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
    Pointer.Execution start.pair.tree [0, 1, 0] out.state.pair.tree (3 + out.cost) ∧
    out.cost ≤ 3968 ∧
    (∀ cut, ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      (Tree.depth middle.tree 1 : ℝ) ≤ 336 + 240 * Real.logb 2 3) ∧
    (∃ first, program [0] = some first ∧ first.instructions <+: out.instructions) ∧
    (∃ rootOut, program [1, 1, 1] = some rootOut ∧ rootOut.instructions = [] ∧
      Pointer.Execution start.pair.tree [1, 1, 1] rootOut.state.pair.tree 3) := by
  obtain ⟨program, start, _, _, _, execute, online⟩ :=
    Deamortization.Weighted.Results.transform (fun _ => scripted) weights source (by decide) positive
  obtain ⟨out, completed, _, _, replay, execution, cost, _, prefixes⟩ :=
    execute [0, 1, 0] (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
  have sourceCost : (scripted.runFrom [] source [0, 1, 0]).1.length = 16 := rfl
  rw [sourceCost] at cost
  refine ⟨program, start, out, completed, replay, execution, cost, ?_, ?_, ?_⟩
  · intro cut
    obtain ⟨middle, first, last, bounds⟩ := prefixes cut
    refine ⟨middle, first, last, ?_⟩
    have bound := bounds ⟨1, by decide⟩
    norm_num [source, leaf, Config.tree, plug, HeavyPath.mass, LabelledTree.inorder, weights] at bound
    exact bound
  · exact online ⟨scripted, fun _ => rfl⟩ [0] [1, 0] out completed
  · obtain ⟨rootOut, rootCompleted, _, _, _, rootExecution, rootCost, _, _⟩ :=
      execute [1, 1, 1] (by norm_num [source, leaf, Config.tree, plug, LabelledTree.erase, Tree.size])
    have sourceEmpty : (scripted.runFrom [] source [1, 1, 1]).1.length = 0 := rfl
    rw [sourceEmpty] at rootCost
    have zero : rootOut.cost = 0 := by omega
    refine ⟨rootOut, rootCompleted, List.length_eq_zero_iff.mp zero, ?_⟩
    simpa only [zero, Nat.add_zero, List.length_cons, List.length_nil] using rootExecution

end RotationBST.Tests.FingerRequests
