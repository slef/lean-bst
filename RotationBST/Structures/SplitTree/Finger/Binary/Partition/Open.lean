module

public import RotationBST.Structures.SplitTree.Finger.Binary.Partition.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

/-- The same local split works before any enclosing separator and larger-key
remainder. Only the two resulting interval views are changed. -/
theorem fingerSplit_open_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) (rest : Tree) :
    let cut := Partition.run h t rank
    Access (openView t rest) (.node (binaryView cut.left.tree).tree (openView cut.right.tree rest))
      rank (fingerSplitOpenCost h t rank) := by
  have split := (Partition.run_spec valid rank existsKey).2
  constructor
  · have first := (openConversion_rotations t rest).symm.append (split.1.inLeft (r := rest))
    have expose : Rotations (.node (Partition.run h t rank).binary rest)
        (.node (Partition.run h t rank).left.tree.binary
          (.node (Partition.run h t rank).right.tree.binary rest)) 1 := .step .right .refl
    have left := (conversion_rotations (Partition.run h t rank).left.tree).inLeft
      (r := .node (Partition.run h t rank).right.tree.binary rest)
    have right := (openConversion_rotations (Partition.run h t rank).right.tree rest).inRight
      (l := (binaryView (Partition.run h t rank).left.tree).tree)
    exact ((first.append expose).append left).append right
  · change (binaryView (Partition.run h t rank).left.tree).tree.size = rank
    rw [binaryView_size]
    exact (Partition.run_sizes valid rank existsKey).1

theorem fingerSplit_open_cost {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : fingerSplitOpenCost h t rank ≤ 23 * h + 1 := by
  have balanced := (Partition.run_spec valid rank existsKey).1
  have heights := Partition.run_height valid rank existsKey
  have split := Partition.run_cost valid rank existsKey
  have initial := openConversion_cost valid
  have left := conversion_cost balanced.1
  have right := openConversion_cost balanced.2
  simp only [fingerSplitOpenCost]
  omega

end RotationBST.SplitTree.Multiway.Finger
