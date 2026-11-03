module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Amortized.Sequence

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Extract.Amortized.Results

/-- Minimum extraction has constant amortized rotation cost in the maintained
finger representation, with a linear initial reserve. -/
theorem repeated_minimum {h : Nat} {t : Multiway} (valid : Balanced h t) (n : Nat) :
    (extractMany n t).2 ≤ 12 * t.nodes + 3 * n ∧
      (extractMany n t).1.size = t.size - n ∧ ∃ k, Balanced k (extractMany n t).1 :=
  ⟨extractMany_cost n valid, extractMany_size n t,
    let ⟨k, balance, _⟩ := extractMany_credit n valid; ⟨k, balance⟩⟩

/-- Extracting every key empties the tree in a linear number of rotations. -/
theorem drain {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (extractMany t.size t).1 = .nil ∧ (extractMany t.size t).2 ≤ 15 * t.size := by
  refine ⟨extractMany_empty t, ?_⟩
  have cost := extractMany_cost t.size valid
  have nodes := nodes_le_size t
  omega

end RotationBST.Arboral.Split.Multiway.Finger.Extract.Amortized.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Extract.Amortized.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Extract.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Extract.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Extract.Amortized.Defs]
