module

public import RotationBST.Bounds.Interleave.Basic

@[expose] public section
namespace RotationBST.Tango

theorem switch_le_one (past : List Bool) (next : Bool) : switch past next ≤ 1 := by
  unfold switch
  split
  · omega
  · split <;> omega

theorem changes_le_height (t : Tree) (past : List Nat) (x : Nat) :
    changes t past x ≤ height t := by
  induction t generalizing past x with
  | nil => simp [changes, height]
  | node l r il ir =>
    have hs := switch_le_one (regions l.size (l.size + 1 + r.size) past) (x ≤ l.size)
    simp only [changes, height]
    split
    · split
      · have := il (leftRequests l.size past) x; omega
      · split
        · omega
        · have := ir (rightRequests l.size past) (x - l.size - 1); omega
    · omega

theorem changeCost_bound (t : Tree) (past xs : List Nat) :
    changeCost t past xs ≤ xs.length * height t := by
  induction xs generalizing past with
  | nil => simp [changeCost]
  | cons x xs ih =>
    have := changes_le_height t past x
    have := ih (past ++ [x])
    simp only [changeCost, List.length_cons, Nat.add_mul]
    omega

theorem interleave_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    interleave t xs ≤ xs.length * height t := by
  have heq := changeCost_eq t [] xs valid
  simp only [List.nil_append, interleave_nil, Nat.zero_add] at heq
  rw [heq]
  exact changeCost_bound t [] xs

theorem perfect_height (h : Nat) : height (perfect h) = h := by
  induction h with
  | zero => rfl
  | succ h ih => simp [perfect, height, ih, Nat.add_comm]

theorem perfect_size (h : Nat) : (perfect h).size = 2 ^ h - 1 := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [perfect, Tree.size, ih, Nat.pow_succ]
    have : 0 < 2 ^ h := Nat.two_pow_pos h
    omega

end RotationBST.Tango
