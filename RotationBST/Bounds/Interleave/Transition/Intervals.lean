module

public import RotationBST.Bounds.Interleave.Transition.Top

@[expose] public section
namespace RotationBST.Wilber

theorem topIn_nested (t : Tree) (lo low high innerLow innerHigh root : Nat)
    (top : topIn t lo low high = some root)
    (lower : low ≤ innerLow) (upper : innerHigh ≤ high)
    (rootlo : innerLow ≤ root) (roothi : root < innerHigh) :
    topIn t lo innerLow innerHigh = some root := by
  induction t generalizing lo with
  | nil => simp [topIn] at top
  | node l r il ir =>
    simp only [topIn] at top ⊢
    split at top
    next h =>
      rw [ite_eq_left (show lo + l.size < innerLow by omega)]
      exact ir (lo + l.size + 1) top
    next h =>
      split at top
      next h' =>
        rw [ite_eq_right (show ¬lo + l.size < innerLow by omega),
          ite_eq_left (show innerHigh ≤ lo + l.size by omega)]
        exact il lo top
      next h' =>
        have he := Option.some.inj top
        rw [ite_eq_right (show ¬lo + l.size < innerLow by omega),
          ite_eq_right (show ¬innerHigh ≤ lo + l.size by omega)]
        exact top

theorem transition_bounds {t : Tree} {low cut high point : Nat}
    (lower : low ≤ cut) (split : cut < high)
    (h : transition t low cut high = some point) : low ≤ point ∧ point < high := by
  unfold transition at h
  split at h
  · contradiction
  · split at h <;> have := topIn_bounds h <;> omega

theorem transition_ne_top {t : Tree} {low cut high point root : Nat}
    (top : topIn t 0 low high = some root)
    (h : transition t low cut high = some point) : point ≠ root := by
  simp only [transition, top] at h
  split at h <;> have := topIn_bounds h <;> omega

theorem transition_exists (t : Tree) (low cut high : Nat)
    (lower : low ≤ cut) (split : cut + 1 < high) (upper : high ≤ t.size) :
    ∃ point, transition t low cut high = some point := by
  obtain ⟨root, top⟩ := topIn_exists t 0 low high (Nat.zero_le _) (by simpa using upper) (by omega)
  simp only [transition, top]
  split
  · exact topIn_exists t 0 (cut + 1) high (Nat.zero_le _) (by simpa using upper) split
  · exact topIn_exists t 0 low (cut + 1) (Nat.zero_le _) (by simp only [Nat.zero_add]; omega) (by omega)

end RotationBST.Wilber
