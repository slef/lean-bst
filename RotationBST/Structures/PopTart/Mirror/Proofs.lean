module

public import RotationBST.Structures.PopTart.Mirror.Definitions.Abstract
public import RotationBST.Models.Pointer.Mirror.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.PopTart.WeightedTree

@[simp] theorem mirror_mirror (t : WeightedTree) : t.mirror.mirror = t := by
  induction t <;> simp_all [mirror]

@[simp] theorem mirror_tree (t : WeightedTree) : t.mirror.tree = t.tree.mirror := by
  induction t <;> simp_all [mirror, tree, skeleton, Pointer.Lazy.Skeleton.tree, Tree.mirror]

@[simp] theorem mirror_mass (t : WeightedTree) : t.mirror.mass = t.mass := by
  induction t <;> simp_all [mirror, mass, add_comm]

theorem mirror_nonnegative {t : WeightedTree} (valid : t.Nonnegative) : t.mirror.Nonnegative := by
  induction t <;> simp_all [mirror, Nonnegative]

theorem mirror_fringe (t : WeightedTree) :
    t.mirror.fringe = (t.fringe.map (fun p => (p.1.mirror, p.2))).reverse := by
  induction t <;> simp_all [mirror, fringe, List.reverse_append]

theorem SlotAt.mirror {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) : SlotAt t.mirror subtree.mirror weight depth := by
  induction slot with
  | leaf t w => exact .leaf t.mirror w
  | left slot ih => exact .right ih
  | right slot ih => exact .left ih

end RotationBST.PopTart.WeightedTree
