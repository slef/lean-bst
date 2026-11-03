module

public import RotationBST.Structures.SplitTree.Finger.Spine

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- Ascending never crosses more ancestors than the stored spine contains. -/
theorem ascend_length (fs : List Frame) (focus : Multiway) (rank : Nat) :
    ascend fs focus rank ≤ fs.length := by
  induction fs generalizing focus with
  | nil => exact Nat.le_refl _
  | cons f fs ih =>
    simp only [ascend]
    split
    · omega
    · have := ih (f.fill focus)
      simp only [List.length_cons]
      omega

/-- If the key is present in the full interval, ascent stops at a containing
ancestor. The untouched suffix of the context still reconstructs the full tree. -/
theorem ascend_contains (fs : List Frame) (focus : Multiway) (rank : Nat)
    (valid : rank < (plug fs focus).size) :
    rank < (plug (fs.take (ascend fs focus rank)) focus).size := by
  induction fs generalizing focus with
  | nil => exact valid
  | cons f fs ih =>
    by_cases inside : rank < focus.size
    · simpa only [ascend, ite_eq_left inside, List.take_zero, plug] using inside
    · have tail := ih (f.fill focus) valid
      simpa only [ascend, ite_eq_right inside, Nat.add_comm 1, List.take_succ_cons, plug] using tail

/-- The geometric growth of balanced intervals bounds ascent from the minimum.
This counts multiway levels only; the comparison-tree realization is separate. -/
theorem ascend_log (fs : List Frame) {h : Nat} {focus : Multiway} (rank : Nat)
    (valid : Valid h fs) (balanced : Balanced h focus)
    (initial : h ≤ Nat.log2 (rank + 1) + 1) :
    ascend fs focus rank + h ≤ Nat.log2 (rank + 1) + 1 := by
  induction fs generalizing h focus with
  | nil => simpa only [ascend, Nat.zero_add] using initial
  | cons f fs ih =>
    by_cases inside : rank < focus.size
    · simpa only [ascend, ite_eq_left inside, Nat.zero_add] using initial
    · have exponential : 2 ^ h ≤ rank + 1 := Nat.le_trans (size_bounds balanced).1 (by omega)
      have level : h ≤ Nat.log2 (rank + 1) := (Nat.le_log2 (by omega)).mpr exponential
      have tail := ih valid.2 (f.balanced valid.1 balanced) (by omega)
      simp only [ascend, ite_eq_right inside]
      omega

/-- The minimum finger reaches a containing ancestor within logarithmically
many levels in the rank, independent of the total tree size. -/
theorem searchLevels_log {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    searchLevels t rank ≤ Nat.log2 (rank + 1) + 1 := by
  exact ascend_log (leftSpine t) rank (leftSpine_balanced valid).1 Balanced.nil (by omega)

theorem searchLevels_contains (t : Multiway) (rank : Nat) (valid : rank < t.size) :
    rank < (plug ((leftSpine t).take (searchLevels t rank)) .nil).size := by
  apply ascend_contains
  rwa [leftSpine_plug]

end RotationBST.SplitTree.Multiway.Finger
