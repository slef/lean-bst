module

public import RotationBST.Structures.SplitTree.Finger.Binary.Search.Height

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open StaticTree

/-- Search in a minimum-finger comparison tree depends on the rank distance,
not the total size. Appending an arbitrary right remainder preserves this bound. -/
theorem extended_depth_rank {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rest : Tree) (rank : Nat) (existsKey : rank < t.size) :
    depth (comb (binaryView t).spine (.node (binaryView t).tail rest)) rank ≤
      5 * Nat.log2 (rank + 1) + 6 := by
  induction valid generalizing rest rank with
  | nil => simp [size] at existsKey
  | @two k a b ha hb ia ib =>
    by_cases left : rank < a.size
    · simpa only [binaryView, comb_append, comb] using ia (.node b.binary rest) rank left
    · have level : k ≤ Nat.log2 (rank + 1) :=
        (Nat.le_log2 (by omega)).mpr (Nat.le_trans (size_bounds ha).1 (by omega))
      have bound := extended_depth_height (Balanced.two ha hb) rest rank existsKey
      omega
  | @three k a b c ha hb hc ia ib ic =>
    by_cases left : rank < a.size
    · simpa only [binaryView, comb_append, comb] using ia (.node b.binary (.node c.binary rest)) rank left
    · have level : k ≤ Nat.log2 (rank + 1) :=
        (Nat.le_log2 (by omega)).mpr (Nat.le_trans (size_bounds ha).1 (by omega))
      have bound := extended_depth_height (Balanced.three ha hb hc) rest rank existsKey
      omega
  | @four k a b c d ha hb hc hd ia ib ic id =>
    by_cases left : rank < a.size
    · simpa only [binaryView, comb_append, comb] using
        ia (.node b.binary (.node c.binary (.node d.binary rest))) rank left
    · have level : k ≤ Nat.log2 (rank + 1) :=
        (Nat.le_log2 (by omega)).mpr (Nat.le_trans (size_bounds ha).1 (by omega))
      have bound := extended_depth_height (Balanced.four ha hb hc hd) rest rank existsKey
      omega

/-- Removing the extra far-right separator cannot lengthen an old search. -/
theorem comb_depth_le_extend (xs : List Tree) (tail rest : Tree) (rank : Nat)
    (valid : rank < (comb xs tail).size) :
    depth (comb xs tail) rank ≤ depth (comb xs (.node tail rest)) rank := by
  induction xs generalizing rank with
  | nil =>
    change rank < tail.size at valid
    simp only [comb, depth, ite_eq_left valid]
    omega
  | cons t xs ih =>
    simp only [comb, depth]
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · have bound := ih (rank - t.size - 1) (by simp only [comb, Tree.size] at valid; omega)
        omega

theorem binaryView_depth {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    depth (binaryView t).tree rank ≤ 5 * Nat.log2 (rank + 1) + 6 := by
  have within : rank < (comb (binaryView t).spine (binaryView t).tail).size := by
    rwa [← BinaryView.tree, binaryView_size]
  exact Nat.le_trans (comb_depth_le_extend _ _ .nil rank within)
    (extended_depth_rank valid .nil rank existsKey)

end RotationBST.Arboral.Split.Multiway.Finger
