module

import RotationBST.Audit.Check
public import RotationBST.Models.Labelled.Mathlib.AbstractBridge
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

/-! An explicit interoperability bridge to Mathlib's standard tree type.
The two elementary conversions are in `Mathlib/Definitions/Abstract`. -/
namespace RotationBST.Representation

theorem from_toBinaryTree (t : Tree) : fromBinaryTree (toBinaryTree t) = t :=
  MathlibBridge.from_to t

theorem to_fromBinaryTree (t : BinaryTree Unit) : toBinaryTree (fromBinaryTree t) = t :=
  MathlibBridge.to_from t

def binaryTreeEquiv : Tree ≃ BinaryTree Unit where
  toFun := toBinaryTree
  invFun := fromBinaryTree
  left_inv := from_toBinaryTree
  right_inv := to_fromBinaryTree

theorem numNodes_toBinaryTree (t : Tree) : (toBinaryTree t).numNodes = t.size :=
  MathlibBridge.numNodes t

end RotationBST.Representation

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Representation allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Mathlib.Definitions.Abstract]
