module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Maximum.Locate.Results

/-- Finger ascent finds a balanced containing interval and retains every outer
ancestor. Its local height is logarithmic in the requested endpoint distance. -/
theorem interval {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    let location := locateMaximum t distance
    Balanced location.height location.focus ∧ Context.Valid location.height location.outer ∧
      Context.plug location.outer location.focus = t ∧ distance < location.focus.size ∧
      location.height ≤ Nat.log2 (distance + 1) + 1 :=
  ⟨(locateMaximum_balance valid distance).1, (locateMaximum_balance valid distance).2, locateMaximum_reconstruct t distance,
    locateMaximum_contains t distance existsKey, locateMaximum_height valid distance⟩

/-- Expose the requested key by splitting only the located interval in the
existing finger BST. Rebalancing its enclosing context is not included. -/
theorem expose {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    Access (maximumView t).tree (splitLocatedMaximum t distance).1 (t.size - 1 - distance) (splitLocatedMaximum t distance).2 ∧
      (splitLocatedMaximum t distance).2 ≤ 23 * (Nat.log2 (distance + 1) + 1) + 1 :=
  splitLocatedMaximum_spec valid distance existsKey

end RotationBST.Arboral.Split.Multiway.Finger.Maximum.Locate.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Locate.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Context.Defs,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs]
