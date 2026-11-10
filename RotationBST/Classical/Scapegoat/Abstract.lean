module

import RotationBST.Audit.Check
public import RotationBST.Classical.Scapegoat.AbstractBridge

@[expose] public section

/-! Scapegoat trees, for a rational `1/2 < α < 1`. `Definitions/Abstract` gives
plain insertion and deletion, the scapegoat search `fix`, the operation `step`
on a state (tree, `N`), `run`, the sizes met by a sequence and the amortized
bound `bound α n`. Costs are those of the dictionary model
(`Models/Dictionary`): `1 + depth` of the place of the change plus rotations. -/
namespace RotationBST.Classical.Scapegoat.Results
open Dictionary

/-- Every operation is a dictionary step, with no data edits. -/
theorem step_dictionary (α : ℚ) (s : State) (op : Op) (valid : op.Valid s.1.size) :
    Dictionary.Step s.1.unit op (step α s op).1.1.unit (step α s op).2 0 :=
  Scapegoat.step_dictionary s op valid

/-- A run is a dictionary execution with the reported cost. -/
theorem run_execution (α : ℚ) (s : State) (ops : List Op) (valid : Op.ValidSeq s.1.size ops) :
    Dictionary.Execution s.1.unit ops (run α s ops).1.1.unit (run α s ops).2 0 :=
  Scapegoat.run_execution s ops valid

/-- **Height.** From the empty tree, every key always lies at depth at most
`log_{1/α} n + 1`. -/
theorem reachable_depth (α : ℚ) (hα : 1 / 2 < α ∧ α < 1) (ops : List Op)
    (valid : Op.ValidSeq 0 ops) (z : Nat) (hz : z < (run α (.nil, 0) ops).1.1.size) :
    ((run α (.nil, 0) ops).1.1.depth z : ℝ) ≤ Real.logb (1 / α) (run α (.nil, 0) ops).1.1.size + 1 :=
  Scapegoat.reachable_depth hα ops valid z hz

/-- **Amortized cost.** From the empty tree, the total cost, rebuilding
included, is at most `∑ bound α nᵢ` over the key counts `nᵢ` met by the
operations: `O(log n)` per operation. -/
theorem total_cost (α : ℚ) (hα : 1 / 2 < α ∧ α < 1) (ops : List Op) (valid : Op.ValidSeq 0 ops) :
    ((run α (.nil, 0) ops).2 : ℝ) ≤ ((sizesFrom 0 ops).map (bound α)).sum :=
  Scapegoat.total_cost hα ops valid

/-- In particular `m` operations from the empty tree cost `O(m log m)`. -/
theorem total_cost_le (α : ℚ) (hα : 1 / 2 < α ∧ α < 1) (ops : List Op) (valid : Op.ValidSeq 0 ops) :
    ((run α (.nil, 0) ops).2 : ℝ) ≤ ops.length * bound α ops.length :=
  Scapegoat.total_cost_le hα ops valid

end RotationBST.Classical.Scapegoat.Results

/-- info: abstract audit passed for `RotationBST.Classical.Scapegoat.Results`: 5 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Classical.Scapegoat.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Dictionary.Definitions.Abstract,
  RotationBST.Classical.Static.Definitions.Abstract,
  RotationBST.Classical.WeightBalanced.Definitions.Abstract,
  RotationBST.Classical.Scapegoat.Definitions.Abstract]
