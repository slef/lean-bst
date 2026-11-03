module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Minimum
public import RotationBST.Structures.SplitTree.Finger.Binary.Search.Access

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Binary.Results

/-- Construct the minimum-finger comparison BST using at most three rotations
per key. Attached subtrees keep their inorder positions and internal shapes. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (binaryView t).tree (viewCost t) ∧ viewCost t ≤ 3 * t.size ∧
      (binaryView t).tree.size = t.size ∧ (binaryView t).spine.length ≤ 3 * h :=
  ⟨binaryView_rotations t, viewCost_linear valid, binaryView_size t, binaryView_length valid⟩

/-- The initialized comparison BST exposes the minimum at its root. -/
theorem minimum (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (binaryView t).tree 0 (viewCost t) := binaryView_minimum t nonempty

/-- Ordinary BST search in the minimum finger has logarithmic rank-distance cost. -/
theorem search_depth {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    StaticTree.depth (binaryView t).tree rank ≤ 5 * Nat.log2 (rank + 1) + 6 :=
  binaryView_depth valid rank existsKey

/-- A concrete splay realizes the same bound in rotations. Its resulting shape
is not claimed to retain the finger representation for the next split. -/
theorem access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (Splay.run (binaryView t).tree rank).1 rank
        (Splay.run (binaryView t).tree rank).2 ∧
      (Splay.run (binaryView t).tree rank).2 ≤ 5 * Nat.log2 (rank + 1) + 6 :=
  binaryView_access valid rank existsKey

end RotationBST.Arboral.Split.Multiway.Finger.Binary.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Binary.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Defs,
  RotationBST.Bounds.StaticTree.Definitions.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Models.Pointer.Model, RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Models.Online.Abstract]
