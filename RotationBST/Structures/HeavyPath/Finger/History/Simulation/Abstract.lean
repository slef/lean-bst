module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Results
open LabelledCursor

theorem step {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential :=
  RotationBST.HeavyPath.Finger.History.Simulation.step valid legal

theorem policy_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyValid weight p :=
  RotationBST.HeavyPath.Finger.History.Simulation.policy_exists weight

theorem run_append {α : Type} (p : Policy α) (c : Config α) (s : State α)
    (xs ys : List Multifinger.Opcode) :
    run p c s (xs ++ ys) = (run p c s xs).bind fun first =>
      (run p first.source first.state ys).map fun last =>
        ⟨last.source, last.state, first.instructions ++ last.instructions⟩ :=
  RotationBST.HeavyPath.Finger.History.Simulation.run_append p c s xs ys

theorem run_prefix {α : Type} (p : Policy α) (c : Config α) (s : State α)
    (xs ys : List Multifinger.Opcode) {out : Output α}
    (completed : run p c s (xs ++ ys) = some out) :
    ∃ first, run p c s xs = some first ∧ first.instructions <+: out.instructions :=
  RotationBST.HeavyPath.Finger.History.Simulation.run_prefix p c s xs ys completed

theorem run_spec {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : sourceRun c ops = some final) :
    ∃ out, run p c s ops = some out ∧ out.source = final ∧
      ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential :=
  RotationBST.HeavyPath.Finger.History.Simulation.run_spec policyValid valid legal

theorem run_none_iff {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (ops : List Multifinger.Opcode) :
    run p c s ops = none ↔ sourceRun c ops = none :=
  RotationBST.HeavyPath.Finger.History.Simulation.run_none_iff policyValid valid ops

theorem initialized_run {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {cs : List (Frame α)}
    {left right : LabelledTree α} {key : α}
    (positive : Positive weight (plug cs (.node left key right))) :
    ∃ (start : State α) (startupCost : Nat),
      ConfigValid weight ⟨.node left key right, cs⟩ start ∧
      Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩ ⟨start.pair.tree, []⟩ startupCost ∧
      startupCost + start.potential ≤ 39 * (plug cs (.node left key right)).erase.size ∧
      ∀ (ops : List Multifinger.Opcode) (final : Config α),
        sourceRun ⟨.node left key right, cs⟩ ops = some final →
        ∃ out, run p ⟨.node left key right, cs⟩ start ops = some out ∧ out.source = final ∧
          ConfigValid weight out.source out.state ∧
          Pointer.Trace ⟨(plug cs (.node left key right)).erase, []⟩
            ⟨out.state.pair.tree, []⟩ (startupCost + out.cost) ∧
          startupCost + out.cost + out.state.potential ≤
            39 * (plug cs (.node left key right)).erase.size + 62 * ops.length :=
  RotationBST.HeavyPath.Finger.History.Simulation.initialized_run policyValid positive

theorem root_key {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) :
    (Pointer.Config.mk s.pair.tree []).key? = c.erase.key? :=
  RotationBST.HeavyPath.Finger.History.Simulation.root_key valid

theorem depth {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (rank : Fin c.tree.inorder.length) :
    (Tree.depth s.pair.tree rank.val : ℝ) ≤
      15 + 15 * Real.logb 2 (HeavyPath.mass weight c.tree /
        weight (c.tree.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.Simulation.depth valid rank

theorem search_walk {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) (rank : Fin c.tree.inorder.length) :
    ∃ (visited : Pointer.Config) (cost : Nat),
      visited.tree = s.pair.tree ∧ visited.key? = some rank.val ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ visited cost ∧
      Pointer.Trace visited ⟨s.pair.tree, []⟩ cost ∧
      (1 + 2 * cost : ℝ) ≤ 31 + 30 * Real.logb 2
        (HeavyPath.mass weight c.tree / weight (c.tree.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.Simulation.search_walk valid rank

theorem step_bounded {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.step_bounded valid legal

theorem policy_bounded_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyBounded weight p :=
  RotationBST.HeavyPath.Finger.History.Simulation.policy_bounded_exists weight

theorem step_within {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 96) ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.step_within valid legal

theorem response_exists_within {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : (perform op c).isSome = true) :
    ∃ out : Output α, perform op c = some out.source ∧ ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
        Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
        ∀ x, Tree.depth middle.tree x ≤ 16 * Tree.depth s.pair.tree x + 96 :=
  RotationBST.HeavyPath.Finger.History.Simulation.response_exists_within valid legal

theorem policy_within_exists {α : Type} (weight : α → ℝ) : ∃ p : Policy α, PolicyWithin weight p :=
  RotationBST.HeavyPath.Finger.History.Simulation.policy_within_exists weight

end RotationBST.HeavyPath.Finger.History.Simulation.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Simulation.Results`: 15 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Simulation.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Invariant.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Recursive.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
