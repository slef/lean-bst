module

public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.LocalAllocation

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

private theorem normalization_before {state : State} (valid : state.HeightValid)
    (rank : Nat) (before : rank < state.left.tree.size) :
    (normalize (expose state rank).left).2 + (normalize (expose state rank).right).2 +
      12 * ((expose state rank).left.nodes + (expose state rank).right.nodes) ≤
      12 * (Fragment.shared state).nodes + 600 * Nat.log2 (rank + 1) + 800 := by
  let cut := splitFromMinimum state.left.tree rank
  let retained : State := ⟨cut.right, state.right⟩
  have pieces := splitFromMinimum_balance valid.1 rank before
  have smallHeight := (Multiway.Partition.run_height (locate_balance valid.1 rank).1 rank
    (locate_contains state.left.tree rank before)).1
  change cut.left.height ≤ (locate state.left.tree rank).height at smallHeight
  have localHeight := locate_height valid.1 rank
  have small := normalize_minimum_cost cut.left pieces.1
  have upper := (repairLocated_balance valid.1 rank before).2
  change cut.right.height ≤ state.left.height at upper
  have gaps := valid.2.2
  have reserve := splitFromMinimum_credit valid.1 rank before
  change cut.cost + 2 * (cut.left.tree.nodes + cut.right.tree.nodes) ≤ _ at reserve
  simp only [expose, before, ite_true, Fragment.nodes]
  change (normalize (.minimum cut.left)).2 + (rebalance retained).2 +
      12 * (cut.left.tree.nodes + (cut.right.tree.nodes + state.right.tree.nodes + 1)) ≤ _
  by_cases ready : retained.left.height ≤ retained.right.height + 1 ∧ retained.right.height ≤ retained.left.height + 1
  · have unchanged : rebalance retained = (retained, 0) := rebalance_unchanged ⟨pieces.2, valid.2.1, ready⟩
    rw [unchanged]
    simp only
    dsimp [retained] at *
    omega
  · have lost : cut.right.height < state.left.height := by
      dsimp [retained] at ready
      omega
    have released := splitFromMinimum_height_loss valid.1 rank before lost
    change cut.left.tree.nodes + cut.right.tree.nodes + state.left.height ≤ _ at released
    have rebuild := (rebalance_spec retained pieces.2 valid.2.1).2.2
    dsimp [retained] at rebuild
    dsimp [retained] at *
    omega

private theorem normalization_after {state : State} (valid : state.HeightValid)
    (rank : Nat) (afterRoot : state.left.tree.size < rank) (existsKey : rank < state.size) :
    (normalize (expose state rank).left).2 + (normalize (expose state rank).right).2 +
      12 * ((expose state rank).left.nodes + (expose state rank).right.nodes) ≤
      12 * (Fragment.shared state).nodes + 600 * Nat.log2 (state.size - 1 - rank + 1) + 800 := by
  have inside : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
  let distance := state.size - 1 - rank
  let cut := splitFromMaximum state.right.tree distance
  let retained : State := ⟨state.left, cut.left⟩
  have pieces := splitFromMaximum_balance valid.2.1 distance inside
  have smallHeight := (Multiway.Partition.run_height (locateMaximum_balance valid.2.1 distance).1 _
    (maximumLocal_rank state.right.tree distance inside)).2
  change cut.right.height ≤ (locateMaximum state.right.tree distance).height at smallHeight
  have localHeight := locateMaximum_height valid.2.1 distance
  have small := normalize_maximum_cost cut.right pieces.2
  have upper := (maximumRepairLocated_balance valid.2.1 distance inside).2
  change cut.left.height ≤ state.right.height at upper
  have gaps := valid.2.2
  have reserve := splitFromMaximum_credit valid.2.1 distance inside
  change cut.cost + 2 * (cut.left.tree.nodes + cut.right.tree.nodes) ≤ _ at reserve
  simp only [expose, show ¬rank < state.left.tree.size by omega,
    show rank ≠ state.left.tree.size by omega, ite_false, Fragment.nodes]
  change (rebalance retained).2 + (normalize (.maximum cut.right)).2 +
      12 * (state.left.tree.nodes + cut.left.tree.nodes + 1 + cut.right.tree.nodes) ≤ _
  by_cases ready : retained.left.height ≤ retained.right.height + 1 ∧ retained.right.height ≤ retained.left.height + 1
  · have unchanged : rebalance retained = (retained, 0) := rebalance_unchanged ⟨valid.1, pieces.1, ready⟩
    rw [unchanged]
    simp only
    dsimp [distance] at localHeight reserve
    dsimp [retained, distance] at *
    omega
  · have lost : cut.left.height < state.right.height := by
      dsimp [retained] at ready
      omega
    have released := splitFromMaximum_height_loss valid.2.1 distance inside lost
    change cut.left.tree.nodes + cut.right.tree.nodes + state.right.height ≤ _ at released
    have rebuild := (rebalance_spec retained valid.1 pieces.1).2.2
    dsimp [retained] at rebuild
    dsimp [distance] at localHeight released
    dsimp [retained, distance] at *
    omega

/-- Complete splitting, including all normalization and rebuild rotations,
has logarithmic amortized cost in the nearer endpoint distance. -/
theorem split_credit {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    (split state rank).cost +
      14 * (intervalNodes (split state rank).left + intervalNodes (split state rank).right) ≤
      14 * (Fragment.shared state).nodes +
        3000 * (Nat.log2 (min rank (state.size - 1 - rank) + 1) + 1) := by
  have exposed := expose_credit state valid.1 valid.2.1 rank existsKey
  have allocation := split_normalization_nodes valid rank existsKey
  have near := chosenDistance_log valid rank existsKey
  by_cases atRoot : rank = state.left.tree.size
  · have leftCost := normalize_minimum_cost state.left valid.1
    have rightCost := normalize_maximum_cost state.right valid.2.1
    have leftNodes := normalize_minimum_nodes state.left
    have rightNodes := normalize_maximum_nodes state.right
    have lowLeft := (size_bounds valid.1).1
    have lowRight := (size_bounds valid.2.1).1
    have hl : state.left.height ≤ Nat.log2 (state.left.tree.size + 1) :=
      (Nat.le_log2 (by omega)).mpr lowLeft
    have hr : state.right.height ≤ Nat.log2 (state.right.tree.size + 1) :=
      (Nat.le_log2 (by omega)).mpr lowRight
    have gaps := valid.2.2
    have sizeEq : state.size - 1 - rank = state.right.tree.size := by simp only [State.size] at *; omega
    simp only [split, expose, atRoot, Nat.lt_irrefl, ite_false, ite_true, Fragment.nodes]
    rw [show state.size - 1 - state.left.tree.size = state.right.tree.size by simp only [State.size]; omega]
    by_cases smaller : state.left.tree.size ≤ state.right.tree.size
    · rw [Nat.min_eq_left smaller]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  · have normalization : (normalize (expose state rank).left).2 + (normalize (expose state rank).right).2 +
        12 * ((expose state rank).left.nodes + (expose state rank).right.nodes) ≤
        12 * (Fragment.shared state).nodes + 600 * Nat.log2 (chosenDistance state rank + 1) + 800 := by
      by_cases before : rank < state.left.tree.size
      · simpa only [chosenDistance, before, ite_true] using normalization_before valid rank before
      · simpa only [chosenDistance, before, atRoot, ite_false] using normalization_after valid rank (by omega) existsKey
    change (expose state rank).cost + (normalize (expose state rank).left).2 +
      (normalize (expose state rank).right).2 + 14 * _ ≤ _
    omega

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
