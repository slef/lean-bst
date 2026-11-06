module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Paired.Population.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Population.Results
open PopTart PopTart.Chocolate LabelledCursor

theorem leaf_count_size (t : WeightedTree) : 1 ≤ t.leafCount ∧ t.leafCount ≤ t.tree.size + 1 :=
  RotationBST.HeavyPath.Paired.Population.leaf_count_size t

theorem pair_population (p : Stacks) :
    1 ≤ p.lower.decode.leafCount ∧ p.lower.decode.leafCount ≤ p.tree.size ∧
    1 ≤ p.upper.decode.leafCount ∧ p.upper.decode.leafCount ≤ p.tree.size :=
  RotationBST.HeavyPath.Paired.Population.pair_population p

theorem push_cost_bound {α : Type} {p : Stacks} (valid : p.Valid) (frame : Frame α)
    {n : Nat} (size : p.tree.size ≤ n) :
    (p.pushCost frame + 1 : ℝ) ≤ 10 + 14 * Real.logb 2 n :=
  RotationBST.HeavyPath.Paired.Population.push_cost_bound valid frame size

theorem expose_cost_bound {α : Type} {p : Stacks} (valid : p.Valid) (frame : Frame α)
    {n : Nat} (size : p.tree.size ≤ n) :
    (p.exposeCost frame : ℝ) ≤ 10 + 10 * Real.logb 2 n :=
  RotationBST.HeavyPath.Paired.Population.expose_cost_bound valid frame size

end RotationBST.HeavyPath.Paired.Population.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Paired.Population.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Paired.Population.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Substitution.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract]
