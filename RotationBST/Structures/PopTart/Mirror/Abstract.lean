module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Mirror.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Mirror.Results
open WeightedTree

theorem involution (t : WeightedTree) : t.mirror.mirror = t := mirror_mirror t
theorem tree (t : WeightedTree) : t.mirror.tree = t.tree.mirror := mirror_tree t
theorem mass (t : WeightedTree) : t.mirror.mass = t.mass := mirror_mass t
theorem nonnegative {t : WeightedTree} (valid : t.Nonnegative) : t.mirror.Nonnegative :=
  mirror_nonnegative valid
theorem fringe (t : WeightedTree) :
    t.mirror.fringe = (t.fringe.map (fun p => (p.1.mirror, p.2))).reverse := mirror_fringe t
theorem slot {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (h : SlotAt t subtree weight depth) : SlotAt t.mirror subtree.mirror weight depth := h.mirror

end RotationBST.PopTart.Mirror.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Mirror.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Mirror.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Mirror.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Mirror.Definitions.Abstract]
