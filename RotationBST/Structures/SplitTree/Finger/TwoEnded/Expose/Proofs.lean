module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs
public import RotationBST.Structures.SplitTree.Finger.Partition.Accounting
public import RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Accounting
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem expose_valid (state : State) (left : state.left.Valid) (right : state.right.Valid)
    (rank : Nat) (existsKey : rank < state.size) :
    (expose state rank).left.Valid ∧ (expose state rank).right.Valid := by
  by_cases before : rank < state.left.tree.size
  · have result := splitFromMinimum_balance left rank before
    exact (by simpa only [expose, before, ite_true, Fragment.Valid] using And.intro result.1 (And.intro result.2 right))
  · by_cases atRoot : rank = state.left.tree.size
    · simpa [expose, atRoot, Fragment.Valid] using And.intro left right
    · have inside : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
      have result := splitFromMaximum_balance right _ inside
      simpa only [expose, before, atRoot, ite_false, Fragment.Valid] using And.intro (And.intro left result.1) result.2

theorem expose_access (state : State) (left : state.left.Valid) (right : state.right.Valid)
    (rank : Nat) (existsKey : rank < state.size) :
    Access state.tree (expose state rank).tree rank (expose state rank).cost := by
  by_cases before : rank < state.left.tree.size
  · have split := splitFromMinimum_access left rank before
    constructor
    · have first := split.1.inLeft (r := (maximumView state.right.tree).tree)
      have finish : Rotations (.node (splitView (splitFromMinimum state.left.tree rank))
          (maximumView state.right.tree).tree)
          (.node (binaryView (splitFromMinimum state.left.tree rank).left.tree).tree
            (.node (binaryView (splitFromMinimum state.left.tree rank).right.tree).tree
              (maximumView state.right.tree).tree)) 1 := .step .right .refl
      simpa only [expose, before, ite_true, Exposure.tree, Fragment.tree, State.tree] using first.append finish
    · simpa only [expose, before, ite_true, Exposure.tree, Fragment.tree, splitView] using split.2
  · by_cases atRoot : rank = state.left.tree.size
    · constructor
      · simp only [expose, atRoot, Nat.lt_irrefl, ite_false, ite_true, Exposure.tree, Fragment.tree, State.tree]
        exact .refl
      · simp [expose, atRoot, Exposure.tree, Fragment.tree, binaryView_size]
    · have inside : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
      have split := splitFromMaximum_access right _ inside
      constructor
      · have first := split.1.inRight (l := (binaryView state.left.tree).tree)
        have finish : Rotations (.node (binaryView state.left.tree).tree
            (maximumSplitView (splitFromMaximum state.right.tree (state.size - 1 - rank))))
            (.node (.node (binaryView state.left.tree).tree
              (maximumView (splitFromMaximum state.right.tree (state.size - 1 - rank)).left.tree).tree)
              (maximumView (splitFromMaximum state.right.tree (state.size - 1 - rank)).right.tree).tree) 1 :=
          .step .left .refl
        simpa only [expose, before, atRoot, ite_false, Exposure.tree, Fragment.tree, State.tree] using first.append finish
      · have sizes := (splitFromMaximum_sizes right _ inside).1
        simp only [expose, before, atRoot, ite_false, Exposure.tree, Fragment.tree, State.tree,
          Tree.size, binaryView_size, maximumView_size]
        simp only [State.size] at *
        omega

theorem expose_sizes (state : State) (left : state.left.Valid) (right : state.right.Valid)
    (rank : Nat) (existsKey : rank < state.size) :
    (expose state rank).left.tree.size = rank ∧
      (expose state rank).right.tree.size = state.size - 1 - rank := by
  have access := expose_access state left right rank existsKey
  have sizes := access.1.size_eq
  simp only [Exposure.tree, Tree.size, state_size] at sizes
  exact ⟨access.2, by have first := access.2; change (expose state rank).left.tree.size = rank at first; omega⟩

/-- Both output reserves are retained in the endpoint-distance accounting. -/
theorem expose_credit (state : State) (left : state.left.Valid) (right : state.right.Valid)
    (rank : Nat) (existsKey : rank < state.size) :
    (expose state rank).cost + 2 * ((expose state rank).left.nodes + (expose state rank).right.nodes) ≤
      2 * (Fragment.shared state).nodes + 85 * Nat.log2 (chosenDistance state rank + 1) + 115 := by
  by_cases before : rank < state.left.tree.size
  · have bound := splitFromMinimum_credit left rank before
    simp only [expose, chosenDistance, before, ite_true, Fragment.nodes]
    omega
  · by_cases atRoot : rank = state.left.tree.size
    · simp only [expose, chosenDistance, atRoot, Nat.lt_irrefl, ite_false, ite_true, Fragment.nodes]
      omega
    · have inside : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
      have bound := splitFromMaximum_credit right _ inside
      simp only [expose, chosenDistance, before, atRoot, ite_false, Fragment.nodes]
      omega

theorem expose_near_credit {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    (expose state rank).cost + 2 * ((expose state rank).left.nodes + (expose state rank).right.nodes) ≤
      2 * (Fragment.shared state).nodes + 170 * Nat.log2 (min rank (state.size - 1 - rank) + 1) + 285 := by
  have bound := expose_credit state valid.1 valid.2.1 rank existsKey
  have near := chosenDistance_log valid rank existsKey
  omega

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
