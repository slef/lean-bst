module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.FingerSimulation
open HeavyPath HeavyPath.Finger.History HeavyPath.Finger.History.Simulation LabelledCursor

private def leaf (key : Nat) : LabelledTree Nat := .node .nil key .nil
private def source : Config Nat := ⟨.node (leaf 1) 2 (leaf 3), []⟩
private def weights (x : Nat) : ℝ := (x : ℝ) + 1

-- All six opcodes occur in a legal round trip, including both rotations.
private def commands : List Multifinger.Opcode :=
  [.downLeft, .upLeft, .downRight, .upRight, .downLeft,
    .rotateLeftChild, .downRight, .rotateRightChild]

private theorem legal : sourceRun source commands = some source := rfl
private theorem positive : Positive weights source.tree := by
  norm_num [source, leaf, Config.tree, plug, Positive, weights]

-- The policy and initialized state are chosen before the entire stream. Its
-- emitted code replays, returns the source finger to the root, and retains
-- bounded depths under nonuniform weights. Startup is charged exactly once.
example : ∃ (p : Policy Nat) (start : State Nat) (startupCost : Nat),
    PolicyValid weights p ∧ ConfigValid weights source start ∧
    ∃ out, run p source start commands = some out ∧ out.source = source ∧
      Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      Pointer.Trace ⟨source.tree.erase, []⟩ ⟨out.state.pair.tree, []⟩ (startupCost + out.cost) ∧
      startupCost + out.cost + out.state.potential ≤ 613 ∧
      (Pointer.Config.mk out.state.pair.tree []).key? = source.erase.key? ∧
      ∀ rank : Fin source.tree.inorder.length,
        (Tree.depth out.state.pair.tree rank.val : ℝ) ≤
          15 + 15 * Real.logb 2 (HeavyPath.mass weights source.tree /
            weights (source.tree.inorder[rank.val]'rank.isLt)) := by
  obtain ⟨p, policyValid⟩ := Simulation.Results.policy_exists weights
  obtain ⟨start, startupCost, valid, _, _, execute⟩ :=
    Simulation.Results.initialized_run policyValid positive
  obtain ⟨out, completed, sourceEq, preserved, trace, bound⟩ := execute commands source legal
  obtain ⟨same, sameRun, _, _, replay, _⟩ := Simulation.Results.run_spec policyValid valid legal
  have sameEq : same = out := Option.some.inj (sameRun.symm.trans completed)
  subst same
  refine ⟨p, start, startupCost, policyValid, valid, out, completed, sourceEq, replay, trace,
    ?_, ?_, ?_⟩
  · exact bound
  · rw [← sourceEq]
    exact Simulation.Results.root_key preserved
  · intro rank
    have atSource : ConfigValid weights source out.state := by simpa only [sourceEq] using preserved
    exact Simulation.Results.depth atSource rank

-- A longer future cannot change the physical instructions already emitted.
example {p : Policy Nat} {start : State Nat} {out : Output Nat}
    (completed : run p source start commands = some out) :
    ∃ earlier, run p source start [.downLeft, .upLeft] = some earlier ∧
      earlier.instructions <+: out.instructions :=
  Simulation.Results.run_prefix p source start [.downLeft, .upLeft]
    [.downRight, .upRight, .downLeft, .rotateLeftChild, .downRight, .rotateRightChild] completed

-- Failure after a valid prefix is preserved; a root cannot move to its parent.
example {p : Policy Nat} (policyValid : PolicyValid weights p) {start : State Nat}
    (valid : ConfigValid weights source start) :
    run p source start [.downLeft, .upLeft, .upLeft] = none :=
  (Simulation.Results.run_none_iff policyValid valid _).mpr rfl

-- The empty stream emits no code and retains the exact history state.
example (p : Policy Nat) (start : State Nat) :
    run p source start [] = some ⟨source, start, []⟩ := rfl

-- The same fixed policy provides startup-inclusive amortized work and a
-- depth bound at every physical prefix of a stream containing all six opcodes.
example : ∃ (p : Policy Nat) (start : State Nat) (startupCost : Nat) (out : Output Nat),
    PolicyBounded (fun _ => 1) p ∧ ConfigValid (fun _ => 1) source start ∧
    run p source start commands = some out ∧ out.source = source ∧
    startupCost + out.cost + out.state.potential ≤ 613 ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < 3, (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 3 := by
  obtain ⟨p, bounded⟩ := Simulation.Results.policy_bounded_exists (fun _ : Nat => (1 : ℝ))
  have positive : Positive (fun _ => 1) source.tree := by
    norm_num [source, leaf, Config.tree, plug, Positive]
  obtain ⟨start, startupCost, valid, _, _, execute⟩ :=
    Simulation.Results.initialized_run bounded.1 positive
  obtain ⟨out, completed, sourceEq, _, _, amortized⟩ := execute commands source legal
  have size : start.pair.tree.size = 3 := Finger.History.Results.state_size valid
  refine ⟨p, start, startupCost, out, bounded, valid, completed, sourceEq, amortized, ?_⟩
  intro cut
  have prefixes := Interruption.Results.run_uniform_prefix bounded valid completed cut
  norm_num only [size, Nat.cast_ofNat] at prefixes
  exact prefixes

-- Nonuniform weights retain the actual accessed-key mass ratio, alongside the
-- explicit population term, throughout a downward response.
example : ∃ (p : Policy Nat) (start : State Nat) (out : Output Nat),
    PolicyBounded weights p ∧ ConfigValid weights source start ∧
    p source start .downLeft = some out ∧
    out.cost + out.state.potential ≤ 62 + start.potential ∧
    (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 3 ∧
    ∀ cut, ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      (Tree.depth middle.tree 0 : ℝ) ≤ 49 + 15 * Real.logb 2 (9 / 2) + 24 * Real.logb 2 3 := by
  obtain ⟨p, bounded⟩ := Simulation.Results.policy_bounded_exists weights
  obtain ⟨start, _, valid, _, _, _⟩ := Simulation.Results.initialized_run bounded.1 positive
  have spec := bounded.1 source start .downLeft valid
  change ∃ out, p source start .downLeft = some out ∧ _ at spec
  obtain ⟨out, responded, _, _, _, _⟩ := spec
  obtain ⟨_, _, amortized, worst, prefixes⟩ := Interruption.Results.response bounded valid responded
  have size : start.pair.tree.size = 3 := Finger.History.Results.state_size valid
  norm_num only [size, Nat.cast_ofNat] at worst
  refine ⟨p, start, out, bounded, valid, responded, amortized, worst, ?_⟩
  intro cut
  obtain ⟨middle, first, last, depths⟩ := prefixes cut
  refine ⟨middle, first, last, ?_⟩
  have bound := depths ⟨0, by decide⟩
  norm_num [size, source, leaf, weights, Config.tree, plug, HeavyPath.mass, LabelledTree.inorder] at bound
  exact bound

-- The whole simulator can be interrupted at any physical cut, including
-- between its internal rotations. The requested key is visited, and the exact
-- original suffix remains executable after returning to the suspended cursor.
example {p : Policy Nat} (bounded : PolicyBounded (fun _ => 1) p) {start : State Nat}
    (valid : ConfigValid (fun _ => 1) source start) {out : Output Nat}
    (completed : Simulation.run p source start commands = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
      ∀ x < 3, ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
        Multifinger.replay before middle = some visited ∧ visited.key? = some x ∧
        Multifinger.replay after visited = some middle ∧
        (1 + before.length + after.length : ℝ) ≤ 197 + 156 * Real.logb 2 3 ∧
        Multifinger.replay (out.instructions.take cut ++ before ++ after ++ out.instructions.drop cut)
          ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ := by
  have size : start.pair.tree.size = 3 := Finger.History.Results.state_size valid
  obtain ⟨middle, first, _, _, requests⟩ := Interruption.Results.run_detour bounded valid completed cut
  refine ⟨middle, first, ?_⟩
  intro x hx
  obtain ⟨visited, before, after, outward, key, backward, work, _, resumed, _, _⟩ :=
    requests x (by rw [size]; exact hx)
  norm_num only [size, Nat.cast_ofNat] at work
  exact ⟨visited, before, after, outward, key, backward, work, resumed⟩

-- A source request already at the root has an empty original program. The
-- window must consume zero original work and emit no detour, regardless of
-- the chosen (sufficient) logarithmic budget.
example {p : Policy Nat} (bounded : PolicyBounded (fun _ => 1) p) {start : State Nat}
    (valid : ConfigValid (fun _ => 1) source start) (budget : Nat)
    (budgetBound : 49 + 39 * Real.logb 2 3 ≤ budget) :
    ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
      Multifinger.replay before ⟨start.pair.tree, []⟩ = some visited ∧ visited.key? = some 1 ∧
      Multifinger.replay after visited = some ⟨start.pair.tree, []⟩ ∧ before = [] ∧ after = [] := by
  have size : start.pair.tree.size = 3 := Finger.History.Results.state_size valid
  have search : Requests.Serves source [] 1 source := ⟨[], [], source, rfl, rfl, rfl, rfl⟩
  have budgetReal : 49 + 39 * Real.logb 2 start.pair.tree.size ≤ budget := by
    simpa only [size, Nat.cast_ofNat] using budgetBound
  obtain ⟨out, consumed, middle, visited, before, after, completed, _, _, _, length,
    first, _, outward, key, backward, work, _, _⟩ := Interruption.Results.search_window bounded valid
      (target := 1) (by rw [size]; decide) search budgetReal
  simp only [Simulation.run, Option.some.injEq] at completed
  subst out
  have zero : consumed = 0 := by simpa using length
  subst consumed
  simp only [List.take_zero, Multifinger.replay, Option.some.injEq] at first
  subst middle
  have lengths : before.length = 0 ∧ after.length = 0 := by omega
  exact ⟨visited, before, after, outward, key, backward,
    List.length_eq_zero_iff.mp lengths.1, List.length_eq_zero_iff.mp lengths.2⟩

end RotationBST.Tests.FingerSimulation
