module

public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs
public import RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Local maximum-finger exposure has logarithmic endpoint-distance cost.
Restoring balance in the enclosing context is a separate operation. -/
theorem splitLocatedMaximum_spec {h : Nat} {t : Multiway} (valid : Balanced h t)
    (distance : Nat) (existsKey : distance < t.size) :
    Access (maximumView t).tree (splitLocatedMaximum t distance).1
      (t.size - 1 - distance) (splitLocatedMaximum t distance).2 ∧
      (splitLocatedMaximum t distance).2 ≤ 23 * (Nat.log2 (distance + 1) + 1) + 1 := by
  have balanced := (locateMaximum_balance valid distance).1
  have contains := locateMaximum_contains t distance existsKey
  have height := locateMaximum_height valid distance
  let rank := (locateMaximum t distance).focus.size - 1 - distance
  have localKey : rank < (locateMaximum t distance).focus.size := by dsimp [rank]; omega
  have sizes := congrArg Tree.size (locateMaximum_view t distance)
  rw [maximumView_size] at sizes
  cases rest : maximumContextRemainder (locateMaximum t distance).outer with
  | none =>
    simp only [maximumEnclosingView, rest, maximumView_size] at sizes
    have rankEq : rank = t.size - 1 - distance := by dsimp [rank]; omega
    have access := maximumSplit_access balanced rank localKey
    have cost := maximumSplit_cost balanced rank localKey
    constructor
    · rw [locateMaximum_view t distance]
      simpa only [maximumEnclosingView, splitLocatedMaximum, rest, ← rankEq] using access
    · simp only [splitLocatedMaximum, rest]
      exact Nat.le_trans cost (by omega)
  | some tail =>
    simp only [maximumEnclosingView, rest] at sizes
    have openSize := (maximumOpen_rotations (locateMaximum t distance).focus tail).size_eq
    simp only [Tree.size, binary_size] at openSize
    have rankEq : tail.size + 1 + rank = t.size - 1 - distance := by dsimp [rank]; omega
    have access := maximumSplit_open_access balanced rank localKey tail
    have cost := maximumSplit_open_cost balanced rank localKey
    constructor
    · rw [locateMaximum_view t distance]
      simp only [rankEq] at access
      simpa only [maximumEnclosingView, splitLocatedMaximum, rest] using access
    · simp only [splitLocatedMaximum, rest]
      exact Nat.le_trans cost (by omega)

end RotationBST.Geometric.Split.Multiway.Finger
