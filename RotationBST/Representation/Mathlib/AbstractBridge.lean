module

public import RotationBST.Representation.Mathlib.Definitions.Abstract

@[expose] public section

namespace RotationBST.Representation.MathlibBridge

theorem from_to (t : Tree) : fromBinaryTree (toBinaryTree t) = t := by
  induction t with
  | nil => rfl
  | node l r il ir => simp [toBinaryTree, fromBinaryTree, il, ir]

theorem to_from (t : BinaryTree Unit) : toBinaryTree (fromBinaryTree t) = t := by
  induction t with
  | nil => rfl
  | node u l r il ir => cases u; simp [toBinaryTree, fromBinaryTree, il, ir]

theorem numNodes (t : Tree) : (toBinaryTree t).numNodes = t.size := by
  induction t with
  | nil => rfl
  | node l r il ir => simp only [toBinaryTree, BinaryTree.numNodes, Tree.size, il, ir]; omega

end RotationBST.Representation.MathlibBridge
