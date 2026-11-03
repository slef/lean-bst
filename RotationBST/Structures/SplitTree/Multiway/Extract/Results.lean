module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Extract.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Extract.Results

/-- Minimum extraction exposes rank zero by actual binary rotations, removes
exactly one key, and preserves balance with at most one level of root shrinkage.
This root-based operation has a height bound, not yet the split-tree finger bound. -/
theorem minimum {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    Access t.binary (.node .nil (t.extractMin).1.binary) 0 (t.extractMin).2 ∧
      (t.extractMin).1.size + 1 = t.size ∧ (t.extractMin).2 ≤ 7 * h ∧
      (Balanced h (t.extractMin).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.extractMin).1) :=
  ⟨extractMin_access t nonempty, extractMin_size t nonempty,
    extractMinAux_cost _ valid (by omega), (extractMinAux_balance _ valid (by omega)).1⟩

/-- A root with at least two keys retains its height after extraction. -/
theorem wide_height {h : Nat} {t : Multiway} (valid : Balanced h t) (wide : Wide t) :
    Balanced h (t.extractMin).1 := (extractMinAux_balance _ valid (by omega)).2 wide

end RotationBST.Arboral.Split.Multiway.Extract.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Extract.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Extract.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Extract.Defs]
