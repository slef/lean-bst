module

public import RotationBST.Splay.Updates.Algorithm.Abstract
public import RotationBST.Splay.Correctness

@[expose] public section

namespace RotationBST.Splay.Updates

/-- The maximum becomes a root with empty right child. -/
theorem run_max (t : Tree) (hne : t ≠ .nil) :
    ∃ l c, run t (t.size - 1) = (.node l .nil, c) ∧
      Access t (.node l .nil) (t.size - 1) c := by
  have hn : 0 < t.size := by cases t <;> simp_all [Tree.size] <;> omega
  have ha := (run_correct t (t.size - 1) (by omega)).1
  rcases he : run t (t.size - 1) with ⟨u, c⟩
  rw [he] at ha
  cases u with
  | nil => exact ha.2.elim
  | node l r =>
      have hs := ha.1.size_eq
      have hk : l.size = t.size - 1 := ha.2
      have hr : r = .nil := by
        cases r with
        | nil => rfl
        | node a b => simp only [Tree.size] at hs; omega
      subst r
      exact ⟨l, c, rfl, ha⟩

/-- Splitting corresponds to a genuine splay of the predecessor, followed by
cutting just its right edge. No key or subtree is discarded. -/
theorem split_spec (t : Tree) (k : Nat) (hk : k ≤ t.size) (hpos : 0 < k) :
    ∃ l r c, Access t (.node l r) (k - 1) c ∧
      split t k = ⟨.node l .nil, r, c⟩ := by
  have ha := (run_correct t (k - 1) (by omega)).1
  rcases he : run t (k - 1) with ⟨u, c⟩
  rw [he] at ha
  cases u with
  | nil => exact ha.2.elim
  | node l r => exact ⟨l, r, c, ha, by simp [split, Nat.ne_of_gt hpos, he]⟩

theorem split_sizes (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    (split t k).left.size = k ∧ (split t k).right.size = t.size - k := by
  by_cases h : k = 0
  · subst k; simp [split, Tree.size]
  · obtain ⟨l, r, c, ha, he⟩ := split_spec t k hk (Nat.pos_of_ne_zero h)
    have hs := ha.1.size_eq
    have hx : l.size = k - 1 := ha.2
    rw [he]
    simp only [Tree.size] at *
    constructor <;> omega

theorem join_size (l r : Tree) : (join l r).1.size = l.size + r.size := by
  cases l with
  | nil => simp [join, Tree.size]
  | node a b =>
      obtain ⟨u, c, he, ha⟩ := run_max (.node a b) (by simp)
      have hs := ha.1.size_eq
      simp only [join, he, Tree.size] at *
      omega

theorem insert_size (t : Tree) (k : Nat) (hk : k ≤ t.size) :
    (insert t k).1.size = t.size + 1 := by
  obtain ⟨hl, hr⟩ := split_sizes t k hk
  simp only [insert, Tree.size, hl, hr]
  omega

theorem delete_size (t : Tree) (x : Nat) (hx : x < t.size) :
    (delete t x).1.size = t.size - 1 := by
  have ha := (run_correct t x hx).1
  rcases he : run t x with ⟨u, c⟩
  rw [he] at ha
  cases u with
  | nil => exact ha.2.elim
  | node l r =>
      have hs := ha.1.size_eq
      simp only [delete, he, join_size]
      simp only [Tree.size] at hs
      omega

end RotationBST.Splay.Updates
