module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem fromRoot_valid {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (fromRoot h t).1.HeightValid :=
  ⟨(Multiway.Partition.children_valid valid).1, (Multiway.Partition.children_valid valid).2,
    Multiway.Partition.children_height_gap valid⟩

theorem fromRoot_rotations (h : Nat) (t : Multiway) (nonempty : t ≠ .nil) :
    Rotations t.binary (fromRoot h t).1.tree (fromRoot h t).2 := by
  rw [Multiway.Partition.children_binary h nonempty]
  exact ((conversion_rotations (Multiway.Partition.children h t).1.tree).inLeft).append
    (maximum_rotations (Multiway.Partition.children h t).2.tree).inRight

theorem fromRoot_cost {h : Nat} {t : Multiway} (valid : Balanced h t) : (fromRoot h t).2 ≤ 6 * h := by
  have parts := Multiway.Partition.children_valid valid
  have left := conversion_cost parts.1
  have right := maximum_cost parts.2
  have heights : (Multiway.Partition.children h t).1.height ≤ h ∧
      (Multiway.Partition.children h t).2.height ≤ h := by
    cases valid <;> simp [Multiway.Partition.children]
  simp only [fromRoot]
  omega

private theorem rank_log_height {h : Nat} {t : Multiway} (valid : Balanced h t)
    {rank : Nat} (existsKey : rank < t.size) : Nat.log2 (rank + 1) ≤ 2 * h := by
  have upper := (size_bounds valid).2
  have power : 4 ^ h = 2 ^ (2 * h) := by rw [Nat.pow_mul]
  rw [power] at upper
  have strict : Nat.log2 (rank + 1) < 2 * h :=
    (Nat.log2_lt (by omega)).mpr (by omega)
  omega

/-- Height balance suffices for a logarithmic nearer-endpoint bound; no
constant ratio between the two subtree sizes is needed. -/
theorem chosenDistance_log {state : State} (valid : state.HeightValid) (rank : Nat)
    (existsKey : rank < state.size) :
    Nat.log2 (chosenDistance state rank + 1) ≤
      2 * Nat.log2 (min rank (state.size - 1 - rank) + 1) + 2 := by
  obtain ⟨left, right, gapLeft, gapRight⟩ := valid
  have lowerLeft := (size_bounds left).1
  have lowerRight := (size_bounds right).1
  by_cases before : rank < state.left.tree.size
  · have upper := rank_log_height left before
    simp only [chosenDistance, before, ite_true]
    by_cases nearer : rank ≤ state.size - 1 - rank
    · rw [Nat.min_eq_left nearer]; omega
    · rw [Nat.min_eq_right (show state.size - 1 - rank ≤ rank by omega)]
      have lower : state.right.height ≤ Nat.log2 (state.size - 1 - rank + 1) :=
        (Nat.le_log2 (by simp only [State.size] at *; omega)).mpr (by simp only [State.size] at *; omega)
      omega
  · by_cases atRoot : rank = state.left.tree.size
    · simp [chosenDistance, atRoot]
    · have within : state.size - 1 - rank < state.right.tree.size := by simp only [State.size] at *; omega
      have upper := rank_log_height right within
      simp only [chosenDistance, before, ite_false, atRoot]
      by_cases nearer : state.size - 1 - rank ≤ rank
      · rw [Nat.min_eq_right nearer]; omega
      · rw [Nat.min_eq_left (show rank ≤ state.size - 1 - rank by omega)]
        have lower : state.left.height ≤ Nat.log2 (rank + 1) :=
          (Nat.le_log2 (by omega)).mpr (by omega)
        omega

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
