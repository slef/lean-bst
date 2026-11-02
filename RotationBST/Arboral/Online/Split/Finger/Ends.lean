module

public import RotationBST.Arboral.Online.Split.Finger.Search

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

@[simp] theorem mirror_size (t : Multiway) : (mirror t).size = t.size := by
  induction t <;> simp_all only [mirror, size] <;> omega

@[simp] theorem mirror_mirror (t : Multiway) : mirror (mirror t) = t := by
  induction t <;> simp_all only [mirror]

theorem mirror_balanced {h : Nat} {t : Multiway} (valid : Balanced h t) : Balanced h (mirror t) := by
  induction valid with
  | nil => exact .nil
  | two ha hb ia ib => exact .two ib ia
  | three ha hb hc ia ib ic => exact .three ic ib ia
  | four ha hb hc hd ia ib ic id => exact .four id ic ib ia

/-- Choosing the nearer finger gives the smaller-side logarithmic level bound. -/
theorem nearSearchLevels_log {h : Nat} {t : Multiway} (valid : Balanced h t) (rank : Nat) :
    nearSearchLevels t rank ≤ Nat.log2 (min rank (t.size - 1 - rank) + 1) + 1 := by
  by_cases nearLeft : rank ≤ t.size - 1 - rank
  · simpa only [nearSearchLevels, ite_eq_left nearLeft, min_eq_left nearLeft] using searchLevels_log valid rank
  · have nearRight : t.size - 1 - rank ≤ rank := by omega
    simpa only [nearSearchLevels, ite_eq_right nearLeft, min_eq_right nearRight] using
      searchLevels_log (mirror_balanced valid) (t.size - 1 - rank)

/-- Mirroring maps every valid original rank to a valid rank from the maximum. -/
theorem right_contains (t : Multiway) (rank : Nat) (valid : rank < t.size) :
    t.size - 1 - rank <
      (Context.plug ((leftSpine (mirror t)).take (searchLevels (mirror t) (t.size - 1 - rank))) .nil).size := by
  apply searchLevels_contains
  rw [mirror_size]
  omega

end RotationBST.Arboral.Split.Multiway.Finger
