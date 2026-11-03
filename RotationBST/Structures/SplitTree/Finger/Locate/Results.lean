module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Locate.Split.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Locate.Results

/-- Finger ascent finds a balanced containing interval and retains every outer
ancestor. Its local height is logarithmic in the requested rank. -/
theorem interval {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    let location := locate t rank
    Balanced location.height location.focus ∧ Context.Valid location.height location.outer ∧
      Context.plug location.outer location.focus = t ∧ rank < location.focus.size ∧
      location.height ≤ Nat.log2 (rank + 1) + 1 :=
  ⟨(locate_balance valid rank).1, (locate_balance valid rank).2, locate_reconstruct t rank,
    locate_contains t rank existsKey, locate_height valid rank⟩

/-- Expose the requested key by splitting only the located interval in the
existing finger BST. Rebalancing its enclosing context is not included. -/
theorem expose {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (splitLocated t rank).1 rank (splitLocated t rank).2 ∧
      (splitLocated t rank).2 ≤ 23 * (Nat.log2 (rank + 1) + 1) + 1 :=
  splitLocated_spec valid rank existsKey

end RotationBST.Arboral.Split.Multiway.Finger.Locate.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Finger.Locate.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Locate.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs]
