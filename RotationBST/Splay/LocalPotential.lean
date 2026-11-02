module

public import RotationBST.Splay.Potential
public import RotationBST.Splay.Logarithms

@[expose] public section

namespace RotationBST.Splay

variable (w : Nat → ℝ) (hw : ∀ i, 0 < w i)
include hw

theorem zig_left (l r b : Tree) (lo : Nat) :
    1 + potential w (.node l (.node r b)) lo - potential w (.node (.node l r) b) lo ≤
      3 * (Real.logb 2 (mass w (.node (.node l r) b) lo) -
        Real.logb 2 (mass w (.node l r) lo)) + 1 := by
  have hm := mass_rotate w (Rotate.right (a := l) (b := r) (c := b)) lo
  have hy := mass_right_le w hw l (.node r b) lo
  rw [← hm] at hy
  have h := zig_inequality (mass_pos w hw l r lo)
    (mass_pos w hw r b (lo + l.size + 1))
    (mass_left_le w hw (.node l r) b lo) hy
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

theorem zig_right (a l r : Tree) (lo : Nat) :
    1 + potential w (.node (.node a l) r) lo - potential w (.node a (.node l r)) lo ≤
      3 * (Real.logb 2 (mass w (.node a (.node l r)) lo) -
        Real.logb 2 (mass w (.node l r) (lo + a.size + 1))) + 1 := by
  have hm := mass_rotate w (Rotate.left (a := a) (b := l) (c := r)) lo
  have hy := mass_left_le w hw (.node a l) r lo
  rw [← hm] at hy
  have h := zig_inequality (mass_pos w hw l r (lo + a.size + 1))
    (mass_pos w hw a l lo) (mass_right_le w hw a (.node l r) lo) hy
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

theorem zigzig_left (l r b c : Tree) (lo : Nat) :
    2 + potential w (.node l (.node r (.node b c))) lo -
      potential w (.node (.node (.node l r) b) c) lo ≤
      3 * (Real.logb 2 (mass w (.node (.node (.node l r) b) c) lo) -
        Real.logb 2 (mass w (.node l r) lo)) := by
  have hr : Rotations (.node (.node (.node l r) b) c)
      (.node l (.node r (.node b c))) 2 := .step .right (.step .right .refl)
  have hm := mass_rotations w hr lo
  have hy := mass_right_le w hw l (.node r (.node b c)) lo
  rw [← hm] at hy
  have hd : mass w (.node l r) lo + mass w (.node b c) (lo + l.size + 1 + r.size + 1) ≤
      mass w (.node (.node (.node l r) b) c) lo := by
    have := hw (lo + l.size + 1 + r.size)
    simp only [Nat.add_assoc] at this
    simp only [mass, Tree.size, Nat.add_assoc]
    linarith
  have h := zigzig_inequality (mass_pos w hw l r lo)
    (mass_pos w hw r (.node b c) (lo + l.size + 1))
    (mass_pos w hw b c (lo + l.size + 1 + r.size + 1))
    (mass_left_le w hw (.node l r) b lo) hy hd
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

theorem zigzig_right (a b l r : Tree) (lo : Nat) :
    2 + potential w (.node (.node (.node a b) l) r) lo -
      potential w (.node a (.node b (.node l r))) lo ≤
      3 * (Real.logb 2 (mass w (.node a (.node b (.node l r))) lo) -
        Real.logb 2 (mass w (.node l r) (lo + a.size + 1 + b.size + 1))) := by
  have hr : Rotations (.node a (.node b (.node l r)))
      (.node (.node (.node a b) l) r) 2 := .step .left (.step .left .refl)
  have hm := mass_rotations w hr lo
  have hy := mass_left_le w hw (.node (.node a b) l) r lo
  rw [← hm] at hy
  have hd : mass w (.node l r) (lo + a.size + 1 + b.size + 1) +
      mass w (.node a b) lo ≤ mass w (.node a (.node b (.node l r))) lo := by
    have := hw (lo + a.size + 1 + b.size)
    simp only [Nat.add_assoc] at this
    simp only [mass, Nat.add_assoc]
    linarith
  have h := zigzig_inequality (mass_pos w hw l r (lo + a.size + 1 + b.size + 1))
    (mass_pos w hw (.node a b) l lo) (mass_pos w hw a b lo)
    (mass_right_le w hw b (.node l r) (lo + a.size + 1)) hy hd
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

theorem zigzag_left (a l r b : Tree) (lo : Nat) :
    2 + potential w (.node (.node a l) (.node r b)) lo -
      potential w (.node (.node a (.node l r)) b) lo ≤
      3 * (Real.logb 2 (mass w (.node (.node a (.node l r)) b) lo) -
        Real.logb 2 (mass w (.node l r) (lo + a.size + 1))) := by
  have hr : Rotations (.node (.node a (.node l r)) b)
      (.node (.node a l) (.node r b)) 2 := .step (.inLeft .left) (.step .right .refl)
  have hm := mass_rotations w hr lo
  have hx := mass_right_le w hw a (.node l r) lo
  have hxz := hx.trans (mass_left_le w hw (.node a (.node l r)) b lo)
  have hd : mass w (.node a l) lo + mass w (.node r b) (lo + a.size + 1 + l.size + 1) ≤
      mass w (.node (.node a (.node l r)) b) lo := by
    have := hw (lo + a.size + 1 + l.size)
    simp only [Nat.add_assoc] at this
    simp only [mass, Tree.size, Nat.add_assoc]
    linarith
  have h := zigzag_inequality (mass_pos w hw l r (lo + a.size + 1))
    (mass_pos w hw a l lo) (mass_pos w hw r b (lo + a.size + 1 + l.size + 1)) hx hxz hd
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

theorem zigzag_right (a l r b : Tree) (lo : Nat) :
    2 + potential w (.node (.node a l) (.node r b)) lo -
      potential w (.node a (.node (.node l r) b)) lo ≤
      3 * (Real.logb 2 (mass w (.node a (.node (.node l r) b)) lo) -
        Real.logb 2 (mass w (.node l r) (lo + a.size + 1))) := by
  have hr : Rotations (.node a (.node (.node l r) b))
      (.node (.node a l) (.node r b)) 2 := .step (.inRight .right) (.step .left .refl)
  have hm := mass_rotations w hr lo
  have hx := mass_left_le w hw (.node l r) b (lo + a.size + 1)
  have hxz := hx.trans (mass_right_le w hw a (.node (.node l r) b) lo)
  have hd : mass w (.node a l) lo + mass w (.node r b) (lo + a.size + 1 + l.size + 1) ≤
      mass w (.node a (.node (.node l r) b)) lo := by
    have := hw (lo + a.size + 1 + l.size)
    simp only [Nat.add_assoc] at this
    simp only [mass, Tree.size, Nat.add_assoc]
    linarith
  have h := zigzag_inequality (mass_pos w hw l r (lo + a.size + 1))
    (mass_pos w hw a l lo) (mass_pos w hw r b (lo + a.size + 1 + l.size + 1)) hx hxz hd
  simp only [potential, Tree.size, Nat.add_assoc]
  rw [← hm]
  simp only [Nat.add_assoc] at h
  linarith

end RotationBST.Splay
