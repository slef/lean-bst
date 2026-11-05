module

public import RotationBST.Bounds.LazyFinger.Sequential.Sequence
public import RotationBST.Bounds.LazyFinger.Edges.Sequence
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

private def remaining (lo hi k : Nat) : Nat :=
  (if k < lo then 1 else 0) + (if k < hi then 1 else 0)

/-- Each adjacent upward step consumes at most one of the two pending interval
boundaries. Empty intervals contribute no crossings. -/
private theorem adjacent_cut (lo hi k : Nat) :
    cut lo hi k (k + 1) + remaining lo hi (k + 1) ≤ remaining lo hi k := by
  unfold cut remaining
  split_ifs <;> omega

private theorem crossings_ascending (lo hi k len : Nat) :
    crossings lo hi k (List.range' (k + 1) len) ≤ remaining lo hi k := by
  induction len generalizing k with
  | zero => simp [crossings, List.range']
  | succ len ih =>
    have next := ih (k + 1)
    have step := adjacent_cut lo hi k
    simp only [List.range', crossings]
    omega

/-- An arbitrary initial move adds at most one crossing; an ascending interval
then crosses at most two boundaries, including when it is a suffix of a scan. -/
theorem crossings_range' (lo hi p start len : Nat) :
    crossings lo hi p (List.range' start len) ≤ 3 := by
  cases len with
  | zero => simp [crossings]
  | succ len =>
    have rest := crossings_ascending lo hi start len
    have first : cut lo hi p start ≤ 1 := by unfold cut; split <;> omega
    have remainingBound : remaining lo hi start ≤ 2 := by unfold remaining; split_ifs <;> omega
    simp only [List.range', crossings]
    omega

/-- An initial move can add one crossing; an ordered scan then crosses at most
two interval boundaries. This holds even for an initial key outside the scan. -/
theorem crossings_range (lo hi p n : Nat) : crossings lo hi p (List.range n) ≤ 3 := by
  rw [List.range_eq_range']
  exact crossings_range' lo hi p 0 n

private def remainingDown (lo hi k : Nat) : Nat :=
  (if lo ≤ k then 1 else 0) + (if hi ≤ k then 1 else 0)

private theorem descending_cut (lo hi k : Nat) :
    cut lo hi (k + 1) k + remainingDown lo hi k ≤ remainingDown lo hi (k + 1) := by
  unfold cut remainingDown
  split_ifs <;> omega

private theorem crossings_descending (lo hi k : Nat) :
    crossings lo hi k (List.range k).reverse ≤ remainingDown lo hi k := by
  induction k with
  | zero => simp [crossings]
  | succ k ih =>
    have step := descending_cut lo hi k
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, crossings]
    omega

/-- Reverse inorder scans have the same three-crossing bound, from any key. -/
theorem crossings_reverse_range (lo hi p n : Nat) :
    crossings lo hi p (List.range n).reverse ≤ 3 := by
  cases n with
  | zero => simp [crossings]
  | succ n =>
    have rest := crossings_descending lo hi n
    have first : cut lo hi p n ≤ 1 := by unfold cut; split <;> omega
    have remainingBound : remainingDown lo hi n ≤ 2 := by unfold remainingDown; split_ifs <;> omega
    simp only [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, crossings]
    omega

theorem crossings_append (lo hi p : Nat) (xs ys : List Nat) :
    crossings lo hi p (xs ++ ys) =
      crossings lo hi p xs + crossings lo hi (xs.getLastD p) ys := by
  induction xs generalizing p with
  | nil => simp [crossings]
  | cons x xs ih => simp only [List.cons_append, crossings, ih, List.getLastD_cons]; omega

theorem crossings_scans (lo hi p n rounds : Nat) : crossings lo hi p (scans n rounds) ≤ 3 * rounds := by
  induction rounds generalizing p with
  | zero => simp [scans, crossings]
  | succ rounds ih =>
    rw [scans, crossings_append]
    have h := crossings_range lo hi p n
    have ht := ih ((List.range n).getLastD p)
    omega

theorem intervalCost_le_size (w : Nat → Nat → Nat) (C : Nat) (hw : ∀ a b, w a b ≤ C)
    (t : Tree) (lo : Nat) : intervalCost w t lo ≤ C * t.size := by
  induction t generalizing lo with
  | nil => simp [intervalCost, Tree.size]
  | node l r ihl ihr =>
    have h := hw lo (lo + (Tree.node l r).size)
    have hl := ihl lo
    have hr := ihr (lo + l.size + 1)
    simp only [intervalCost, Tree.size] at *
    nlinarith

/-- Every fixed BST serves repeated scans in linear lazy-finger cost, uniformly
in its shape and in the valid initial finger. -/
theorem scans_costFrom (t : Tree) (p rounds : Nat) (hp : p < t.size) :
    costFrom t p (scans t.size rounds) ≤ 4 * rounds * t.size := by
  rw [costFrom_eq_crossings t p _ hp (scans_valid t.size rounds), scans_length]
  have h := intervalCost_le_size (fun a b => crossings a b p (scans t.size rounds)) (3 * rounds)
    (fun a b => crossings_scans a b p t.size rounds) t 0
  nlinarith

theorem scans_cost (t : Tree) (rounds : Nat) :
    cost t (scans t.size rounds) ≤ 4 * rounds * t.size := by
  cases t with
  | nil => simp [cost, scans_length, Tree.size]
  | node l r =>
    exact scans_costFrom (.node l r) l.size rounds (by simp [Tree.size]; omega)

end RotationBST.LazyFinger
