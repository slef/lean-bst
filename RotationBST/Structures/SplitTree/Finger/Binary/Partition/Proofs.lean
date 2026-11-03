module

public import RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Bounds
public import RotationBST.Structures.SplitTree.Multiway.Partition.Cost.Proofs
public import RotationBST.Models.Rotation.Connectivity.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

theorem fingerSplit_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (splitView (fingerSplit h t rank)) rank (fingerSplit h t rank).cost := by
  have split := (Partition.run_spec valid rank existsKey).2
  constructor
  · have first := (conversion_rotations t).symm.append split.1
    have left := (conversion_rotations (Partition.run h t rank).left.tree).inLeft
      (r := (Partition.run h t rank).right.tree.binary)
    have right := (conversion_rotations (Partition.run h t rank).right.tree).inRight
      (l := (binaryView (Partition.run h t rank).left.tree).tree)
    exact (first.append left).append right
  · change (binaryView (Partition.run h t rank).left.tree).tree.size = rank
    rw [binaryView_size]
    exact (Partition.run_sizes valid rank existsKey).1

theorem fingerSplit_cost {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : (fingerSplit h t rank).cost ≤ 23 * h := by
  have balanced := (Partition.run_spec valid rank existsKey).1
  have heights := Partition.run_height valid rank existsKey
  have split := Partition.run_cost valid rank existsKey
  have initial := conversion_cost valid
  have left := conversion_cost balanced.1
  have right := conversion_cost balanced.2
  simp only [fingerSplit]
  omega

end RotationBST.SplitTree.Multiway.Finger
