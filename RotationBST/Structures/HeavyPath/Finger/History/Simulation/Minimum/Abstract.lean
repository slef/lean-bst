module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation.Minimum.Results
open LabelledCursor

theorem potential_le {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : potential weight c ≤ s.potential :=
  RotationBST.HeavyPath.Finger.History.Simulation.Minimum.potential_le valid

theorem attained {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) :
    ∃ best, ConfigValid weight c best ∧ best.potential = potential weight c :=
  RotationBST.HeavyPath.Finger.History.Simulation.Minimum.attained valid

theorem excess_add {α : Type} {weight : α → ℝ} {c : Config α} {s : State α}
    (valid : ConfigValid weight c s) : excess weight c s + potential weight c = s.potential :=
  RotationBST.HeavyPath.Finger.History.Simulation.Minimum.excess_add valid

theorem potential_drop {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} (finalValid : ConfigValid weight final s)
    (legal : sourceRun c ops = some final) :
    potential weight c ≤ 186 * ops.length + potential weight final :=
  RotationBST.HeavyPath.Finger.History.Simulation.Minimum.potential_drop policyValid finalValid legal

theorem run_excess {α : Type} {weight : α → ℝ} {p : Policy α}
    (policyValid : PolicyValid weight p) {c final : Config α} {s : State α}
    {ops : List Multifinger.Opcode} {out : Output α} (valid : ConfigValid weight c s)
    (legal : sourceRun c ops = some final) (completed : run p c s ops = some out) :
    out.cost + excess weight out.source out.state ≤ 248 * ops.length + excess weight c s :=
  RotationBST.HeavyPath.Finger.History.Simulation.Minimum.run_excess policyValid valid legal completed

end RotationBST.HeavyPath.Finger.History.Simulation.Minimum.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.History.Simulation.Minimum.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.History.Simulation.Minimum.Results allowing [
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
  RotationBST.Structures.HeavyPath.Finger.History.Simulation.Minimum.Definitions.Abstract]
