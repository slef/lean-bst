module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.AbstractBridge

@[expose] public section

/-! Split trees: unlabelled 2–3–4 trees (`Multiway/Abstract`) viewed as binary
comparison trees, with a minimum or maximum finger (`Finger/Abstract`,
`Finger/Binary/Abstract`). They represent last-touch supernodes in the causal
geometric simulation. The statements below are the contract that simulation
uses: constant-cost construction, logarithmic finger search in rank distance,
and linear total accounting over a split hierarchy. Rebalancing, joins, and
two-ended fingers are internal `Results` modules reachable from the bridge. -/
namespace RotationBST.Geometric.Split.Results

/-- Construct the minimum-finger comparison BST using at most three rotations
per key. Attached subtrees keep their inorder positions and internal shapes. -/
theorem finger_construction {h : Nat} {t : Multiway} (valid : Multiway.Balanced h t) :
    Rotations t.binary (Multiway.Finger.binaryView t).tree (Multiway.Finger.viewCost t) ∧
      Multiway.Finger.viewCost t ≤ 3 * t.size ∧
      (Multiway.Finger.binaryView t).tree.size = t.size ∧
      (Multiway.Finger.binaryView t).spine.length ≤ 3 * h :=
  Multiway.Finger.Binary.Results.construction valid

/-- The initialized comparison BST exposes the minimum at its root. -/
theorem finger_minimum (t : Multiway) (nonempty : t ≠ .nil) :
    Access t.binary (Multiway.Finger.binaryView t).tree 0 (Multiway.Finger.viewCost t) :=
  Multiway.Finger.Binary.Results.minimum t nonempty

/-- Ordinary BST search in the minimum finger has logarithmic rank-distance cost. -/
theorem finger_search_depth {h : Nat} {t : Multiway} (valid : Multiway.Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Tree.depth (Multiway.Finger.binaryView t).tree rank ≤ 5 * Nat.log2 (rank + 1) + 6 :=
  Multiway.Finger.Binary.Results.search_depth valid rank existsKey

/-- A concrete splay realizes the same bound in rotations. -/
theorem finger_access {h : Nat} {t : Multiway} (valid : Multiway.Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (Multiway.Finger.binaryView t).tree
        (Splay.run (Multiway.Finger.binaryView t).tree rank).1 rank
        (Splay.run (Multiway.Finger.binaryView t).tree rank).2 ∧
      (Splay.run (Multiway.Finger.binaryView t).tree rank).2 ≤ 5 * Nat.log2 (rank + 1) + 6 :=
  Multiway.Finger.Binary.Results.access valid rank existsKey

/-- The minimum finger reconstructs the original tree with one frame per level. -/
theorem finger_representation {h : Nat} {t : Multiway} (valid : Multiway.Balanced h t) :
    Multiway.Context.plug (Multiway.Finger.leftSpine t) .nil = t ∧
      Multiway.Context.Valid 0 (Multiway.Finger.leftSpine t) ∧
      (Multiway.Finger.leftSpine t).length = h :=
  Multiway.Finger.Results.representation valid

/-- Ascending from the nearer endpoint costs logarithmically many multiway
levels in the smaller side. -/
theorem nearer_endpoint {h : Nat} {t : Multiway} (valid : Multiway.Balanced h t) (rank : Nat) :
    Multiway.Finger.nearSearchLevels t rank ≤ Nat.log2 (min rank (t.size - 1 - rank) + 1) + 1 :=
  Multiway.Finger.Results.nearer_endpoint valid rank

/-- Smaller-side logarithmic charges sum to at most twice the number of keys,
for every complete split hierarchy. This is the accounting lemma; a BST split
implementation and its per-operation bound are separate obligations. -/
theorem linear_accounting (hierarchy : Tree) : totalCharge hierarchy ≤ 2 * hierarchy.size :=
  totalCharge_linear hierarchy

end RotationBST.Geometric.Split.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Online.Abstract, RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Abstract, RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Finger.Abstract, RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Accounting.Abstract]
