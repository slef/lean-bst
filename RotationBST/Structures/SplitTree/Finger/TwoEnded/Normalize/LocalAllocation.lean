module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Allocation
public import RotationBST.Structures.SplitTree.Finger.Partition.HeightLoss
public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.HeightLoss

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

/-- Normalization creates only logarithmically many new reserve nodes, even
when endpoint conversions traverse the full height of a large remaining side. -/
theorem split_normalization_nodes {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    intervalNodes (split state rank).left + intervalNodes (split state rank).right ≤
      (expose state rank).left.nodes + (expose state rank).right.nodes +
        3 * Nat.log2 (chosenDistance state rank + 1) + 10 := by
  by_cases before : rank < state.left.tree.size
  · have lower := splitFromMinimum_height_gap valid.1 rank before
    have upper := (repairLocated_balance valid.1 rank before).2
    change (splitFromMinimum state.left.tree rank).right.height ≤ state.left.height at upper
    have gapLeft := valid.2.2.1
    have gapRight := valid.2.2.2
    have gap : (splitFromMinimum state.left.tree rank).right.height - state.right.height +
        (state.right.height - (splitFromMinimum state.left.tree rank).right.height) ≤ Nat.log2 (rank + 1) + 2 := by omega
    have small := normalize_minimum_nodes (splitFromMinimum state.left.tree rank).left
    have large := rebalance_nodes_gap ⟨(splitFromMinimum state.left.tree rank).right, state.right⟩
    simp only [Fragment.nodes] at large
    simp only [split, expose, before, ite_true, chosenDistance, Fragment.nodes]
    change intervalNodes (normalize (.minimum (splitFromMinimum state.left.tree rank).left)).1 +
      intervalNodes (some (rebalance ⟨(splitFromMinimum state.left.tree rank).right, state.right⟩).1) ≤ _
    omega
  · by_cases atRoot : rank = state.left.tree.size
    · have left := normalize_minimum_nodes state.left
      have right := normalize_maximum_nodes state.right
      simp only [split, expose, chosenDistance, atRoot, Nat.lt_irrefl, ite_false, ite_true, Fragment.nodes]
      omega
    · have inside : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
      have lower := splitFromMaximum_height_gap valid.2.1 _ inside
      have upper := (maximumRepairLocated_balance valid.2.1 _ inside).2
      change (splitFromMaximum state.right.tree (state.size - 1 - rank)).left.height ≤ state.right.height at upper
      have gapLeft := valid.2.2.1
      have gapRight := valid.2.2.2
      have gap : state.left.height - (splitFromMaximum state.right.tree (state.size - 1 - rank)).left.height +
          ((splitFromMaximum state.right.tree (state.size - 1 - rank)).left.height - state.left.height) ≤
          Nat.log2 (state.size - 1 - rank + 1) + 2 := by omega
      have small := normalize_maximum_nodes (splitFromMaximum state.right.tree (state.size - 1 - rank)).right
      have large := rebalance_nodes_gap ⟨state.left, (splitFromMaximum state.right.tree (state.size - 1 - rank)).left⟩
      simp only [Fragment.nodes] at large
      simp only [split, expose, before, atRoot, ite_false, chosenDistance, Fragment.nodes]
      change intervalNodes (some (rebalance ⟨state.left, (splitFromMaximum state.right.tree (state.size - 1 - rank)).left⟩).1) +
        intervalNodes (normalize (.maximum (splitFromMaximum state.right.tree (state.size - 1 - rank)).right)).1 ≤ _
      omega

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
