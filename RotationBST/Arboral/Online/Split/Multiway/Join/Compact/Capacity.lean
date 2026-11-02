module

public import RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Height

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Join

theorem rootKeys_bound (t : Multiway) : rootKeys t ≤ 3 := by
  cases t <;> simp [rootKeys]

/-- Joining two pieces below a height ceiling either stays below it, or reaches
it with a minimal root. This is the invariant needed when rebuilding a split. -/
theorem compact_below {hl hr h : Nat} {l r : Multiway}
    (left : Balanced hl l) (right : Balanced hr r) (belowLeft : hl < h) (belowRight : hr < h) :
    4 * (compact hl hr l r).height + rootKeys (compact hl hr l r).tree ≤ 4 * h + 1 := by
  have bounds := (compact_balance left right).2
  have keys := rootKeys_bound (compact hl hr l r).tree
  by_cases growth : max hl hr < (compact hl hr l r).height
  · have minimal := compact_growth hl hr l r growth
    omega
  · omega

/-- A piece no larger than a minimal root can join a minimal sibling without
exceeding that sibling's height. Equal heights use zero-rotation absorption. -/
theorem compact_with_two_left {h hr : Nat} {a b r : Multiway}
    (left : Balanced h (.two a b)) (right : Balanced hr r)
    (capacity : 4 * hr + rootKeys r ≤ 4 * h + 1) :
    4 * (compact h hr (.two a b) r).height + rootKeys (compact h hr (.two a b) r).tree ≤ 4 * h + 3 := by
  have le : hr ≤ h := by omega
  by_cases smaller : hr < h
  · obtain ⟨height, keys⟩ := compact_taller_two_left smaller a b r
    omega
  · have eq : hr = h := by omega
    subst hr
    cases r with
    | nil => cases right; cases left
    | two c d => simp [compact, rootKeys]
    | three c d e => simp only [rootKeys] at capacity; omega
    | four c d e f => simp only [rootKeys] at capacity; omega

theorem compact_with_two_right {hl h : Nat} {l a b : Multiway}
    (left : Balanced hl l) (right : Balanced h (.two a b))
    (capacity : 4 * hl + rootKeys l ≤ 4 * h + 1) :
    4 * (compact hl h l (.two a b)).height + rootKeys (compact hl h l (.two a b)).tree ≤ 4 * h + 3 := by
  have le : hl ≤ h := by omega
  by_cases smaller : hl < h
  · obtain ⟨height, keys⟩ := compact_taller_two_right smaller l a b
    omega
  · have eq : hl = h := by omega
    subst hl
    cases l with
    | nil => cases left; cases right
    | two c d => simp [compact, rootKeys]
    | three c d e => simp only [rootKeys] at capacity; omega
    | four c d e f => simp only [rootKeys] at capacity; omega

/-- Joining below a ceiling to a piece bounded by a minimal root at that
ceiling leaves at most two root separators at the ceiling. -/
theorem compact_below_minimal_right {hl hr h : Nat} {l r : Multiway}
    (left : Balanced hl l) (right : Balanced hr r) (below : hl < h)
    (capacity : 4 * hr + rootKeys r ≤ 4 * h + 1) :
    4 * (compact hl hr l r).height + rootKeys (compact hl hr l r).tree ≤ 4 * h + 2 := by
  have le : hr ≤ h := by omega
  by_cases smaller : hr < h
  · have bound := compact_below left right below smaller
    omega
  · have eq : hr = h := by omega
    subst hr
    cases r with
    | nil => cases right; omega
    | two a b =>
      obtain ⟨height, keys⟩ := compact_taller_two_right below l a b
      omega
    | three a b c => simp only [rootKeys] at capacity; omega
    | four a b c d => simp only [rootKeys] at capacity; omega

end RotationBST.Arboral.Split.Multiway.Join
