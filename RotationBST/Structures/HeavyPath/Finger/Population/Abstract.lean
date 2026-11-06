module

import RotationBST.Audit.Check
public import RotationBST.Structures.HeavyPath.Finger.Population.AbstractBridge

@[expose] public section
namespace RotationBST.HeavyPath.Finger.Population.Results
open PopTart PopTart.Chocolate

theorem pair_population (p : Pair) :
    1 ≤ p.lower.decode.leafCount ∧ p.lower.decode.leafCount ≤ p.tree.size ∧
    1 ≤ p.upper.decode.leafCount ∧ p.upper.decode.leafCount ≤ p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.pair_population p

theorem lower_push {p : Pair} (valid : p.Valid) :
    (p.lower.pushCost : ℝ) ≤ 6 + 14 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.lower_push valid

theorem upper_push {p : Pair} (valid : p.Valid) :
    (p.upper.pushCost : ℝ) ≤ 6 + 14 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.upper_push valid

theorem lower_pop {p : Pair} (valid : p.Valid) :
    (p.lower.popCost : ℝ) ≤ 6 + 10 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.lower_pop valid

theorem upper_pop {p : Pair} (valid : p.Valid) :
    (p.upper.popCost : ℝ) ≤ 6 + 10 * Real.logb 2 p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.upper_pop valid

theorem lower_payload_size {p : Pair} {shape : Tree} {charge : ℝ}
    (stored : p.lower.top = .leaf shape.mirror charge) : shape.size ≤ p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.lower_payload_size stored

theorem upper_payload_size {p : Pair} {shape : Tree} {charge : ℝ}
    (stored : p.upper.top = .leaf shape charge) : shape.size ≤ p.tree.size :=
  RotationBST.HeavyPath.Finger.Population.upper_payload_size stored

end RotationBST.HeavyPath.Finger.Population.Results

/-- info: abstract audit passed for `RotationBST.HeavyPath.Finger.Population.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.HeavyPath.Finger.Population.Results allowing [
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
  RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Definitions.Abstract,
  RotationBST.Structures.HeavyPath.Finger.Transfer.Definitions.Abstract,
  RotationBST.Structures.PopTart.Chocolate.Top.Definitions.Abstract]
