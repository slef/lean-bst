module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Endpoint
public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Bounds
public import RotationBST.Structures.SplitTree.Multiway.Partition.Cost.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded

theorem state_size (state : State) : state.tree.size = state.size := by
  simp only [State.tree, State.size, Tree.size, binaryView_size, maximumView_size]

theorem make_rotations (h : Nat) (t : Multiway) (valid : Balanced h t) (nonempty : t ≠ .nil) :
    Rotations t.binary (make h t).1.tree (make h t).2 := by
  have positive : 0 < t.size := by cases t <;> simp_all [size]
  have split := (Multiway.Partition.run_spec valid ((t.size - 1) / 2) (by omega)).2.1
  have left := (conversion_rotations (Multiway.Partition.run h t ((t.size - 1) / 2)).left.tree).inLeft
    (r := (Multiway.Partition.run h t ((t.size - 1) / 2)).right.tree.binary)
  have right := (maximum_rotations (Multiway.Partition.run h t ((t.size - 1) / 2)).right.tree).inRight
    (l := (binaryView (Multiway.Partition.run h t ((t.size - 1) / 2)).left.tree).tree)
  exact (split.append left).append right

theorem make_valid {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    (make h t).1.Valid := by
  have positive : 0 < t.size := by cases t <;> simp_all [size]
  have balanced := (Multiway.Partition.run_spec valid ((t.size - 1) / 2) (by omega)).1
  have sizes := Multiway.Partition.run_sizes valid ((t.size - 1) / 2) (by omega)
  refine ⟨balanced.1, balanced.2, ?_, ?_⟩ <;> simp only [make] <;> omega

theorem make_cost {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    (make h t).2 ≤ 20 * h := by
  have positive : 0 < t.size := by cases t <;> simp_all [size]
  have balanced := (Multiway.Partition.run_spec valid ((t.size - 1) / 2) (by omega)).1
  have heights := Multiway.Partition.run_height valid ((t.size - 1) / 2) (by omega)
  have split := Multiway.Partition.run_cost valid ((t.size - 1) / 2) (by omega)
  have left := conversion_cost balanced.1
  have right := maximum_cost balanced.2
  simp only [make]
  omega

/-- Size balance makes the endpoint selected by the root comparison within a
factor of two of the nearer endpoint, even when the selected side is larger. -/
theorem chosenDistance_bound {state : State} (valid : state.Valid) (rank : Nat)
    (existsKey : rank < state.size) :
    chosenDistance state rank + 1 ≤ 2 * (min rank (state.size - 1 - rank) + 1) := by
  obtain ⟨_, _, left, right⟩ := valid
  unfold chosenDistance
  simp only [State.size] at *
  split <;> (try split) <;> omega

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded
