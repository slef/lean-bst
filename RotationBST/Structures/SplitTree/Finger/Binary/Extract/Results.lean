module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Bounds

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Extract.Results

/-- Minimum extraction preserves the finger representation and balance, removes
one key, and uses at most three rotations per level. This is a height bound;
linear total splitting cost requires a further amortized analysis. -/
theorem minimum {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    Access (binaryView t).tree (.node .nil (binaryView (extractView t).1).tree) 0 (extractView t).2 ∧
      (extractView t).1.size + 1 = t.size ∧ (extractView t).2 ≤ 3 * h ∧
      (Balanced h (extractView t).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (extractView t).1) :=
  ⟨extractView_access valid nonempty, extractMin_size t nonempty,
    (extractFingerAux_cost _ valid (by omega)).2,
    (extractMinAux_balance _ valid (by omega)).1⟩

/-- Extraction composes with any larger-key remainder without changing it. -/
theorem before_remainder {h : Nat} {t : Multiway} (valid : Balanced h t)
    (nonempty : t ≠ .nil) (rest : Tree) :
    Rotations (openView t rest) (.node .nil (openView (extractView t).1 rest))
      (extractOpenCost (t.nodes + 1) t) ∧ extractOpenCost (t.nodes + 1) t ≤ 3 * h :=
  ⟨(extractFingerAux_rotations _ valid (by omega) nonempty).1 rest,
    (extractFingerAux_cost _ valid (by omega)).1⟩

end RotationBST.Arboral.Split.Multiway.Finger.Extract.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Extract.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Extract.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Extract.Defs]
