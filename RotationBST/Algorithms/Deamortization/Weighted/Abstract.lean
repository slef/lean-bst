module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Deamortization.Weighted.AbstractBridge

@[expose] public section
namespace RotationBST.Deamortization.Weighted.Results
open HeavyPath.Finger.History

theorem simulation {α : Type} (weight : α → ℝ) (c : LabelledCursor.Config α)
    (live : c.focus ≠ .nil) (positive : HeavyPath.Positive weight c.tree) :
    ∃ (p : Simulation.Policy α) (start : State α) (startup : Nat),
      Simulation.PolicyWithin weight p ∧ Simulation.ConfigValid weight c start ∧
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨start.pair.tree, []⟩ startup ∧
      startup ≤ 16 * c.tree.erase.size ∧
      ∀ (a : Simulation.Requests.Algorithm α) (past keys : List Nat),
        (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, Simulation.Requests.run p a past c start keys = some out ∧
          out.source = (a.runFrom past c keys).2 ∧
          Simulation.ConfigValid weight out.source out.state ∧
          Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          out.cost ≤ 248 * (a.runFrom past c keys).1.length ∧
          (Pointer.Config.mk out.state.pair.tree []).key? = out.source.erase.key? ∧
          ∀ cut, ∃ middle,
            Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
            Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
            ∀ rank : Fin c.tree.inorder.length,
              (Tree.depth middle.tree rank.val : ℝ) ≤
                336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
                  weight (c.tree.inorder[rank.val]'rank.isLt)) :=
  RotationBST.Deamortization.Weighted.simulation weight c live positive

theorem online_prefix {α : Type} (p : Simulation.Policy α)
    (a : Simulation.Requests.Algorithm α) (past : List Nat) (c : LabelledCursor.Config α)
    (start : State α) (xs ys : List Nat) {out : Simulation.Output α}
    (completed : Simulation.Requests.run p a past c start (xs ++ ys) = some out) :
    ∃ first, Simulation.Requests.run p a past c start xs = some first ∧
      first.instructions <+: out.instructions :=
  RotationBST.Deamortization.Weighted.online_prefix p a past c start xs ys completed

theorem transform {α : Type} (family : List Nat → Simulation.Requests.Algorithm α)
    (weight : α → ℝ) (c : LabelledCursor.Config α) (live : c.focus ≠ .nil)
    (positive : HeavyPath.Positive weight c.tree) :
    ∃ (program : List Nat → Option (Simulation.Output α)) (start : State α) (startup : Nat),
      Pointer.Trace ⟨c.tree.erase, []⟩ ⟨start.pair.tree, []⟩ startup ∧
      startup ≤ 16 * c.tree.erase.size ∧
      (∀ keys, (∀ x ∈ keys, x < c.tree.erase.size) →
        ∃ out, program keys = some out ∧
          out.source = ((family keys).runFrom [] c keys).2 ∧
          Simulation.ConfigValid weight out.source out.state ∧
          Multifinger.replay out.instructions ⟨start.pair.tree, []⟩ = some ⟨out.state.pair.tree, []⟩ ∧
          Pointer.Execution start.pair.tree keys out.state.pair.tree (keys.length + out.cost) ∧
          out.cost ≤ 248 * ((family keys).runFrom [] c keys).1.length ∧
          (Pointer.Config.mk out.state.pair.tree []).key? = out.source.erase.key? ∧
          ∀ cut, ∃ middle,
            Multifinger.replay (out.instructions.take cut) ⟨start.pair.tree, []⟩ = some middle ∧
            Multifinger.replay (out.instructions.drop cut) middle = some ⟨out.state.pair.tree, []⟩ ∧
            ∀ rank : Fin c.tree.inorder.length,
              (Tree.depth middle.tree rank.val : ℝ) ≤
                336 + 240 * Real.logb 2 (HeavyPath.mass weight c.tree /
                  weight (c.tree.inorder[rank.val]'rank.isLt))) ∧
      ((∃ a, ∀ keys, family keys = a) →
        ∀ xs ys out, program (xs ++ ys) = some out →
          ∃ first, program xs = some first ∧ first.instructions <+: out.instructions) :=
  RotationBST.Deamortization.Weighted.transform family weight c live positive

end RotationBST.Deamortization.Weighted.Results

/-- info: abstract audit passed for `RotationBST.Deamortization.Weighted.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Deamortization.Weighted.Results allowing [
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
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Requests.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
