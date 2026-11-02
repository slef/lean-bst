module

public import RotationBST.Model.Abstract
public import Mathlib.Data.Nat.Log

@[expose] public section
namespace RotationBST.Arboral.Split

/-- Charge for splitting around one key, with `left` and `right` keys remaining.
This measures the smaller-side search term, not an implemented BST operation. -/
def charge (left right : Nat) : Nat := 1 + Nat.log2 (min left right + 1)

/-- A binary tree records a complete split hierarchy: its root is removed first,
then the two resulting intervals are split in arbitrary interleaved order. -/
def totalCharge : Tree → Nat
  | .nil => 0
  | .node l r => totalCharge l + totalCharge r + charge l.size r.size

end RotationBST.Arboral.Split
