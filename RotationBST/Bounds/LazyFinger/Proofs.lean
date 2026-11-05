module

public import RotationBST.Bounds.LazyFinger.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem distance_le_depths (t : Tree) (x y : Nat) :
    distance t x y ≤ Tree.depth t x + Tree.depth t y := by
  induction t generalizing x y with
  | nil => simp [distance]
  | node l r ihl ihr =>
    simp only [distance]
    split
    · rename_i h
      have := ihl x y
      simp [Tree.depth, h.1, h.2]
      omega
    · split
      · rename_i h
        have := ihr (x - l.size - 1) (y - l.size - 1)
        simp [Tree.depth, Nat.not_lt.mpr (Nat.le_of_lt h.1),
          Nat.not_lt.mpr (Nat.le_of_lt h.2), Nat.ne_of_gt h.1, Nat.ne_of_gt h.2]
        omega
      · exact le_rfl

theorem distance_self (t : Tree) (x : Nat) (hx : x < t.size) :
    distance t x x = 0 := by
  induction t generalizing x with
  | nil => simp [Tree.size] at hx
  | node l r ihl ihr =>
    simp only [distance]
    split
    · rename_i h; exact ihl x h.1
    · split
      · rename_i h
        apply ihr
        simp only [Tree.size] at hx
        omega
      · rename_i h₁ h₂
        have : x = l.size := by omega
        simp [this, Tree.depth]

theorem distance_symm (t : Tree) (x y : Nat) : distance t x y = distance t y x := by
  induction t generalizing x y with
  | nil => rfl
  | node l r ihl ihr =>
    simp only [distance]
    simp only [and_comm (a := y < l.size), and_comm (a := l.size < y)]
    split
    · exact ihl x y
    · split
      · exact ihr _ _
      · omega

theorem costFrom_le (t : Tree) (p : Nat) (xs : List Nat) :
    costFrom t p xs ≤ Tree.depth t p + 2 * StaticTree.cost t xs := by
  induction xs generalizing p with
  | nil => simp [costFrom, StaticTree.cost]
  | cons x xs ih =>
    have h := ih x
    have hd := distance_le_depths t p x
    simp only [costFrom, StaticTree.cost, List.map_cons, List.sum_cons] at *
    omega

theorem cost_le_twice_static (t : Tree) (xs : List Nat) :
    cost t xs ≤ 2 * StaticTree.cost t xs := by
  cases t with
  | nil => simp [cost, StaticTree.cost, Tree.depth]; omega
  | node l r =>
    have h := costFrom_le (.node l r) l.size xs
    simpa [cost, Tree.depth] using h

theorem length_le_costFrom (t : Tree) (p : Nat) (xs : List Nat) :
    xs.length ≤ costFrom t p xs := by
  induction xs generalizing p with
  | nil => simp [costFrom]
  | cons x xs ih =>
    have := ih x
    simp only [List.length_cons, costFrom]
    omega

end RotationBST.LazyFinger
