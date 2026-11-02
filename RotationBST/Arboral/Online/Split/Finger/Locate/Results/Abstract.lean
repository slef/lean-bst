module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Locate.Split.Proofs

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

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Locate.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract]
