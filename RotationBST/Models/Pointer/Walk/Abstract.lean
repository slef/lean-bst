module

import RotationBST.Audit.Check
public import RotationBST.Models.Pointer.Walk.AbstractBridge

@[expose] public section
namespace RotationBST.Pointer.Walk.Results

theorem primitive {a b : Config} (move : Move a b) : Step a b := move.step

theorem physical {a b : Config} {k : Nat} (walk : Walk a b k) : Trace a b k := walk.trace

theorem fixed_tree {a b : Config} {k : Nat} (walk : Walk a b k) : a.tree = b.tree := walk.tree_eq

end RotationBST.Pointer.Walk.Results

/-- info: abstract audit passed for `RotationBST.Pointer.Walk.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Pointer.Walk.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Pointer.Walk.Definitions.Abstract]
