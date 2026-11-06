module

import RotationBST.Audit.Check
public import RotationBST.Structures.PopTart.Located.AbstractBridge

@[expose] public section
namespace RotationBST.PopTart.Located.Results
open WeightedTree

theorem fringeSpan_append (xs ys : List (Tree × ℝ)) :
    fringeSpan (xs ++ ys) = fringeSpan xs + fringeSpan ys :=
  RotationBST.PopTart.WeightedTree.fringeSpan_append xs ys

theorem fringeSpan_fringe (t : WeightedTree) : fringeSpan t.fringe = t.tree.size + 1 :=
  RotationBST.PopTart.WeightedTree.fringeSpan_fringe t

theorem forget {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) : SlotAt t subtree weight depth :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.forget slot

theorem fits {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) : offset + subtree.size ≤ t.tree.size :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.fits slot

theorem split {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) :
    ∃ before after, t.fringe = before ++ (subtree, weight) :: after ∧ fringeSpan before = offset :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.split slot

theorem locate_split {t : WeightedTree} {before after : List (Tree × ℝ)} {subtree : Tree} {weight : ℝ}
    (split : t.fringe = before ++ (subtree, weight) :: after) :
    ∃ depth, LocatedSlot t subtree weight (fringeSpan before) depth :=
  RotationBST.PopTart.WeightedTree.locate_split split

theorem key_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (x : Nat) (inside : x < subtree.size) :
    Tree.depth t.tree (offset + x) = depth + Tree.depth subtree x :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.key_depth slot x inside

theorem successor_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (existsKey : offset + subtree.size < t.tree.size) :
    Tree.depth t.tree (offset + subtree.size) < depth :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.successor_depth slot existsKey

theorem predecessor_depth {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) (existsKey : 0 < offset) :
    Tree.depth t.tree (offset - 1) < depth :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.predecessor_depth slot existsKey

theorem context {t : WeightedTree} {subtree : Tree} {weight : ℝ} {offset depth : Nat}
    (slot : LocatedSlot t subtree weight offset depth) :
    ∃ cs : List Pointer.Frame, cs.length = depth ∧ Pointer.offset cs = offset ∧ Pointer.plug cs subtree = t.tree :=
  RotationBST.PopTart.WeightedTree.LocatedSlot.context slot

end RotationBST.PopTart.Located.Results

/-- info: abstract audit passed for `RotationBST.PopTart.Located.Results`: 10 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.PopTart.Located.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.PopTart.Definitions.Abstract,
  RotationBST.Structures.PopTart.Located.Definitions.Abstract]
