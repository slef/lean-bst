module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Interruption.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Interruption.Results
open LabelledCursor

theorem response {α : Type} {weight : α → ℝ} {p : Policy α}
    (bounded : PolicyBounded weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) :
    ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
        Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
        ∀ rank : Fin c.tree.inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            49 + 15 * Real.logb 2 (HeavyPath.mass weight c.tree /
              weight (c.tree.inorder[rank.val]'rank.isLt)) +
                24 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.response bounded valid responded

theorem response_uniform {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < s.pair.tree.size,
        (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.response_uniform bounded valid responded cut

theorem run_uniform_prefix {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ x < s.pair.tree.size,
        (Tree.depth middle.tree x : ℝ) ≤ 49 + 39 * Real.logb 2 s.pair.tree.size :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.run_uniform_prefix bounded valid completed cut

theorem run_detour {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      middle.focus ≠ .nil ∧
      ∀ x < s.pair.tree.size, ∃ (visited : Pointer.Config) (before after : List Multifinger.Opcode),
        Multifinger.replay before middle = some visited ∧ visited.key? = some x ∧
        Multifinger.replay after visited = some middle ∧
        (1 + before.length + after.length : ℝ) ≤ 197 + 156 * Real.logb 2 s.pair.tree.size ∧
        (middle.key? = some x → before = [] ∧ after = []) ∧
        Multifinger.replay (out.instructions.take cut ++ before ++ after ++ out.instructions.drop cut)
          ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
        (∀ pause, ∃ cursor, Multifinger.replay (before.take pause) middle = some cursor ∧
          cursor.tree = middle.tree) ∧
        (∀ pause, ∃ cursor, Multifinger.replay (after.take pause) visited = some cursor ∧
          cursor.tree = middle.tree) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.run_detour bounded valid completed cut

theorem search_window {α : Type} {p : Policy α}
    (bounded : PolicyBounded (fun _ => 1) p) {c final : Config α} {s : State α}
    (valid : ConfigValid (fun _ => 1) c s) {ops : List Multifinger.Opcode} {target budget : Nat}
    (targetValid : target < s.pair.tree.size) (search : Requests.Serves c ops target final)
    (budgetBound : 49 + 39 * Real.logb 2 s.pair.tree.size ≤ budget) :
    ∃ (out : Output α) (consumed : Nat) (middle visited : Pointer.Config)
      (before after : List Multifinger.Opcode),
      run p c s ops = some out ∧ out.source = final ∧
      out.cost + out.state.potential ≤ 62 * ops.length + s.potential ∧
      consumed ≤ budget ∧ consumed ≤ out.instructions.length ∧
      Multifinger.replay (out.instructions.take consumed) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop consumed) middle = some ⟨out.state.pair.tree, []⟩ ∧
      Multifinger.replay before ⟨s.pair.tree, []⟩ = some visited ∧ visited.key? = some target ∧
      Multifinger.replay after visited = some middle ∧
      before.length + after.length ≤ 5 * consumed ∧
      1 + before.length + after.length ≤ 1 + 5 * budget ∧
      (consumed = budget ∨ middle.key? = some target) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.search_window bounded valid targetValid search budgetBound

theorem response_weighted {α : Type} {weight : α → ℝ} {p : Policy α}
    (certified : PolicyWithin weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {op : Multifinger.Opcode} {out : Output α}
    (responded : p c s op = some out) :
    ConfigValid weight out.source out.state ∧
      Multifinger.replay out.instructions ⟨s.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
      out.cost + out.state.potential ≤ 62 + s.potential ∧
      (out.cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size ∧
      ∀ cut, ∃ middle,
        Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
        Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
        ∀ rank : Fin c.tree.inorder.length,
          (Tree.depth middle.tree rank.val : ℝ) ≤
            336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
              weight (c.tree.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.response_weighted certified valid responded

theorem run_weighted_prefix {α : Type} {weight : α → ℝ} {p : Policy α}
    (certified : PolicyWithin weight p) {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) {ops : List Multifinger.Opcode} {out : Output α}
    (completed : run p c s ops = some out) (cut : Nat) :
    ∃ middle,
      Multifinger.replay (out.instructions.take cut) ⟨s.pair.tree, []⟩ = some middle ∧
      Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
      ∀ rank : Fin c.tree.inorder.length,
        (Tree.depth middle.tree rank.val : ℝ) ≤
          336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
            weight (c.tree.inorder[rank.val]'rank.isLt)) :=
  RotationBST.HeavyPath.Finger.History.Simulation.Interruption.run_weighted_prefix certified valid completed cut

end RotationBST.HeavyPath.Finger.History.Simulation.Interruption.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Simulation.Interruption.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Simulation.Interruption.Results allowing [
  RotationBST.Models.Rotation.Abstract,
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
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract]
