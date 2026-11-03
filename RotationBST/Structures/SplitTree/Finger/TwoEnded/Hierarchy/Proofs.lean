module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Accounting
public import RotationBST.Structures.SplitTree.Accounting.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem hierarchy_rotations (hierarchy : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = hierarchy.size) :
    Rotations (intervalTree input) hierarchy (hierarchyCost hierarchy input) := by
  induction hierarchy generalizing input with
  | nil =>
    cases input with
    | none => exact .refl
    | some state => simp only [intervalTree, state_size, State.size, Tree.size] at sizes; omega
  | node l r il ir =>
    cases input with
    | none => simp only [intervalTree, Tree.size] at sizes; omega
    | some state =>
      have existsKey : l.size < state.size := by simp only [intervalTree, state_size, Tree.size] at sizes; omega
      have access := split_access valid l.size existsKey
      have parts := split_sizes valid l.size existsKey
      have good := split_valid valid l.size existsKey
      have rightSize : (intervalTree (split state l.size).right).size = r.size := by
        simp only [intervalTree, state_size, Tree.size] at sizes
        omega
      have left := il (split state l.size).left good.1 parts.1
      have right := ir (split state l.size).right good.2 rightSize
      exact (access.1.append left.inLeft).append right.inRight

/-- Every internal split passes its reserves to its two recursive calls, so
only the initial reserve and the hierarchy's smaller-side charges remain. -/
theorem hierarchy_credit (hierarchy : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = hierarchy.size) :
    hierarchyCost hierarchy input ≤ 14 * intervalNodes input + 3000 * totalCharge hierarchy := by
  induction hierarchy generalizing input with
  | nil => simp [hierarchyCost, totalCharge]
  | node l r il ir =>
    cases input with
    | none => simp [hierarchyCost]
    | some state =>
      have existsKey : l.size < state.size := by simp only [intervalTree, state_size, Tree.size] at sizes; omega
      have parts := split_sizes valid l.size existsKey
      have good := split_valid valid l.size existsKey
      have rightSize : (intervalTree (split state l.size).right).size = r.size := by
        simp only [intervalTree, state_size, Tree.size] at sizes
        omega
      have left := il (split state l.size).left good.1 parts.1
      have right := ir (split state l.size).right good.2 rightSize
      have cost := split_credit valid l.size existsKey
      have distance : state.size - 1 - l.size = r.size := by
        simp only [intervalTree, state_size, Tree.size] at sizes
        omega
      rw [distance] at cost
      simp only [hierarchyCost, totalCharge, charge, intervalNodes, Fragment.nodes] at *
      omega

theorem intervalNodes_le_size (input : Option State) : intervalNodes input ≤ (intervalTree input).size := by
  cases input with
  | none => exact Nat.le_refl _
  | some state =>
    have left := nodes_le_size state.left.tree
    have right := nodes_le_size state.right.tree
    simp only [intervalNodes, intervalTree, state_size, State.size]
    omega

/-- An arbitrary complete split hierarchy has linear total rotation cost. -/
theorem hierarchy_linear (hierarchy : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = hierarchy.size) :
    hierarchyCost hierarchy input ≤ 6014 * hierarchy.size := by
  have credit := hierarchy_credit hierarchy input valid sizes
  have reserve := intervalNodes_le_size input
  have charges := totalCharge_linear hierarchy
  omega

/-- Include establishing the two endpoints from an ordinary balanced encoding. -/
theorem hierarchy_from_balanced {h : Nat} {t : Multiway} (valid : Balanced h t)
    (nonempty : t ≠ .nil) (hierarchy : Tree) (sizes : t.size = hierarchy.size) :
    Rotations t.binary hierarchy
      ((fromRoot h t).2 + hierarchyCost hierarchy (some (fromRoot h t).1)) ∧
      (fromRoot h t).2 + hierarchyCost hierarchy (some (fromRoot h t).1) ≤
        6014 * hierarchy.size + 6 * h := by
  have setup := fromRoot_rotations h t nonempty
  have validState := fromRoot_valid valid
  have sameSize : (intervalTree (some (fromRoot h t).1)).size = hierarchy.size := by
    have same := setup.size_eq
    rw [binary_size] at same
    exact same.symm.trans sizes
  have steps := hierarchy_rotations hierarchy (some (fromRoot h t).1) validState sameSize
  have cost := hierarchy_linear hierarchy (some (fromRoot h t).1) validState sameSize
  have initial := fromRoot_cost valid
  exact ⟨setup.append steps, by omega⟩

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
