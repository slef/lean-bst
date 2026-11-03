module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Proofs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Cost.Proofs
public import RotationBST.Models.Rotation.Connectivity.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

theorem maximumSplit_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (maximumView t).tree (maximumSplitView (maximumSplit h t rank)) rank (maximumSplit h t rank).cost := by
  have split := (Partition.run_spec valid rank existsKey).2
  constructor
  · have first := (maximum_rotations t).symm.append split.1
    have left := (maximum_rotations (Partition.run h t rank).left.tree).inLeft
      (r := (Partition.run h t rank).right.tree.binary)
    have right := (maximum_rotations (Partition.run h t rank).right.tree).inRight
      (l := (maximumView (Partition.run h t rank).left.tree).tree)
    exact (first.append left).append right
  · change (maximumView (Partition.run h t rank).left.tree).tree.size = rank
    rw [maximumView_size]
    exact (Partition.run_sizes valid rank existsKey).1

theorem maximumSplit_cost {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : (maximumSplit h t rank).cost ≤ 23 * h := by
  have balanced := (Partition.run_spec valid rank existsKey).1
  have heights := Partition.run_height valid rank existsKey
  have split := Partition.run_cost valid rank existsKey
  have initial := maximum_cost valid
  have left := maximum_cost balanced.1
  have right := maximum_cost balanced.2
  simp only [maximumSplit]
  omega

/-- Splitting a maximum-finger interval preserves an arbitrary smaller-key
remainder. The target rank includes this remainder and its separator. -/
theorem maximumSplit_open_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) (rest : Tree) :
    let cut := Partition.run h t rank
    Access (maximumOpenView t rest)
      (.node (maximumOpenView cut.left.tree rest) (maximumView cut.right.tree).tree)
      (rest.size + 1 + rank) (maximumSplitOpenCost h t rank) := by
  have split := (Partition.run_spec valid rank existsKey).2
  constructor
  · have first := (maximumOpen_rotations t rest).symm.append (split.1.inRight (l := rest))
    have expose : Rotations (.node rest (Partition.run h t rank).binary)
        (.node (.node rest (Partition.run h t rank).left.tree.binary)
          (Partition.run h t rank).right.tree.binary) 1 := .step .left .refl
    have left := (maximumOpen_rotations (Partition.run h t rank).left.tree rest).inLeft
      (r := (Partition.run h t rank).right.tree.binary)
    have right := (maximum_rotations (Partition.run h t rank).right.tree).inRight
      (l := maximumOpenView (Partition.run h t rank).left.tree rest)
    exact ((first.append expose).append left).append right
  · change (maximumOpenView (Partition.run h t rank).left.tree rest).size = _
    have sizes := (maximumOpen_rotations (Partition.run h t rank).left.tree rest).size_eq
    have rankEq := (Partition.run_sizes valid rank existsKey).1
    simp only [Tree.size, binary_size] at sizes
    omega

theorem maximumSplit_open_cost {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : maximumSplitOpenCost h t rank ≤ 23 * h + 1 := by
  have balanced := (Partition.run_spec valid rank existsKey).1
  have heights := Partition.run_height valid rank existsKey
  have split := Partition.run_cost valid rank existsKey
  have initial := maximumOpen_cost valid
  have left := maximumOpen_cost balanced.1
  have right := maximum_cost balanced.2
  simp only [maximumSplitOpenCost]
  omega

end RotationBST.Geometric.Split.Multiway.Finger
