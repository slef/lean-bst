module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.WeightedTree.Results

theorem mass_nonnegative {t : WeightedTree} (nonnegative : t.Nonnegative) : 0 ≤ t.mass :=
  RotationBST.PopTart.WeightedTree.mass_nonnegative nonnegative

theorem slot_le_mass {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) (nonnegative : t.Nonnegative) :
    0 ≤ weight ∧ weight ≤ t.mass :=
  RotationBST.PopTart.WeightedTree.slot_le_mass slot nonnegative

theorem slot_context {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = t.tree :=
  RotationBST.PopTart.WeightedTree.slot_context slot

theorem slot_trace {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) (nonempty : subtree ≠ .nil) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.plug cs subtree = t.tree ∧
      Pointer.Trace ⟨t.tree, []⟩ ⟨subtree, cs⟩ depth :=
  RotationBST.PopTart.WeightedTree.slot_trace slot nonempty

theorem perfect_count {level : Nat} {crumb : WeightedTree} (perfect : Perfect level crumb) :
    leafCount crumb = 2 ^ level :=
  RotationBST.PopTart.WeightedTree.perfect_count perfect

theorem perfect_depth {level : Nat} {crumb : WeightedTree} (perfect : Perfect level crumb)
    {subtree : Tree} {weight : ℝ} {depth : Nat} (slot : WeightedTree.SlotAt crumb subtree weight depth) :
    depth = level :=
  RotationBST.PopTart.WeightedTree.perfect_depth perfect slot

theorem height_slot (t : WeightedTree) :
    ∃ subtree weight depth, SlotAt t subtree weight depth ∧ depth = t.height :=
  RotationBST.PopTart.WeightedTree.height_slot t

theorem empty_count {t : WeightedTree} (empty : t.EmptyFringe) : leafCount t = t.tree.size + 1 :=
  RotationBST.PopTart.WeightedTree.empty_count empty

theorem key_depth_lt_height {t : WeightedTree} (empty : t.EmptyFringe) (x : Nat) (valid : x < t.tree.size) :
    Tree.depth t.tree x < t.height :=
  RotationBST.PopTart.WeightedTree.key_depth_lt_height empty x valid

theorem fringe_length (t : WeightedTree) : t.fringe.length = t.leafCount :=
  RotationBST.PopTart.WeightedTree.fringe_length t

theorem fringe_mass (t : WeightedTree) : (t.fringe.map Prod.snd).sum = t.mass :=
  RotationBST.PopTart.WeightedTree.fringe_mass t

theorem fringe_nonnegative (t : WeightedTree) :
    t.Nonnegative ↔ ∀ p ∈ t.fringe, 0 ≤ p.2 :=
  RotationBST.PopTart.WeightedTree.fringe_nonnegative t

theorem slot_split {t : WeightedTree} {subtree : Tree} {weight : ℝ} {depth : Nat}
    (slot : SlotAt t subtree weight depth) :
    ∃ before after, t.fringe = before ++ (subtree, weight) :: after :=
  RotationBST.PopTart.WeightedTree.slot_split slot

theorem ordered_append {t a b : WeightedTree} (split : t.fringe = a.fringe ++ b.fringe) :
    t.Ordered ↔ a.Ordered ∧ b.Ordered ∧
      ∀ x ∈ a.fringe, ∀ y ∈ b.fringe, y.2 ≤ x.2 :=
  RotationBST.PopTart.WeightedTree.ordered_append split

theorem ordered_prefix_mass {t : WeightedTree} (ordered : t.Ordered)
    {before after : List (Tree × ℝ)} {subtree : Tree} {weight : ℝ}
    (split : t.fringe = before ++ (subtree, weight) :: after) :
    ((before.length + 1 : Nat) : ℝ) * weight ≤ t.mass :=
  RotationBST.PopTart.WeightedTree.ordered_prefix_mass ordered split

end RotationBST.PopTart.WeightedTree.Results

/-- info: abstract audit passed for `RotationBST.PopTart.WeightedTree.Results`: 15 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.WeightedTree.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract]
