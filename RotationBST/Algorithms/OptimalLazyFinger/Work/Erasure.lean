module

public import RotationBST.Algorithms.OptimalLazyFinger.Work.Primitives
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work
open Cslib.Algorithms.Lean

@[simp] theorem matrixGet_ret (t : PrefixSum.Table) (a b : Nat) :
    (matrixGet t a b).ret = PrefixSum.get t a b := rfl

@[simp] theorem increment_ret (t : PrefixSum.Table) (a b : Nat) :
    (increment t a b).ret = Preprocessing.increment t a b := rfl

@[simp] theorem fill_ret (t : PrefixSum.Table) (p : Nat) (xs : List Nat) :
    (fill t p xs).ret = Preprocessing.fill t p xs := by
  induction xs generalizing t p with
  | nil => rfl
  | cons x xs ih => simp [fill, Preprocessing.fill, ih]

@[simp] theorem frequencies_ret (n p : Nat) (xs : List Nat) :
    (frequencies n p xs).ret = Preprocessing.frequencies n p xs := by
  simp [frequencies, Preprocessing.frequencies]

@[simp] theorem row_ret (f : Nat → Computation Nat) (n : Nat) :
    (row f n).ret = PrefixSum.row (fun i => (f i).ret) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [row, PrefixSum.row, ih]

@[simp] theorem build_ret (f : Nat → Nat → Computation Nat) (width height : Nat) :
    (build f width height).ret = PrefixSum.build (fun a b => (f a b).ret) width height := by
  induction height with
  | zero => simp [build, PrefixSum.build]
  | succ height ih => simp [build, PrefixSum.build, ih]

@[simp] theorem prepare_ret (n p : Nat) (xs : List Nat) :
    (prepare n p xs).ret = Preprocessing.prepare n p xs := by
  simp [prepare, Preprocessing.prepare]

@[simp] theorem rectangle_ret (p : PrefixSum.Table) (a b c d : Nat) :
    (rectangle p a b c d).ret = PrefixSum.rectangle p a b c d := rfl

@[simp] theorem toll_ret (p : PrefixSum.Table) (n lo hi : Nat) :
    (toll p n lo hi).ret = Preprocessing.toll p n lo hi := rfl

@[simp] theorem minimum_ret (initial : Entry) (xs : List Entry) :
    (minimum initial xs).ret = OptimalLazyFinger.minimum initial xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [minimum, OptimalLazyFinger.minimum, ih]

@[simp] theorem candidate_ret (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (n lo k : Nat) :
    (candidate w previous n lo k).ret =
      (.node (lookup previous k lo).1 (lookup previous (n - k) (lo + k + 1)).1,
        (w lo (lo + n + 1)).ret + (lookup previous k lo).2 +
          (lookup previous (n - k) (lo + k + 1)).2) := rfl

@[simp] theorem cell_ret (w : Nat → Nat → Computation Nat) (previous : Array (Array Entry))
    (N n lo : Nat) :
    (cell w previous N n lo).ret =
      if lo + n + 1 ≤ N then
        let c (k : Fin (n + 1)) : Entry :=
          (.node (lookup previous k.val lo).1 (lookup previous (n - k.val) (lo + k.val + 1)).1,
            (w lo (lo + n + 1)).ret + (lookup previous k.val lo).2 +
              (lookup previous (n - k.val) (lo + k.val + 1)).2)
        OptimalLazyFinger.minimum (c ⟨0, Nat.zero_lt_succ n⟩) ((List.finRange (n + 1)).map c)
      else (.nil, 0) := by
  by_cases h : lo + n + 1 ≤ N <;> simp [cell, h]

@[simp] theorem tabulate_ret (w : Nat → Nat → Computation Nat) (N n : Nat) :
    (tabulate w N n).ret = OptimalLazyFinger.tabulate (fun a b => (w a b).ret) N n := by
  induction n with
  | zero => simp [tabulate, OptimalLazyFinger.tabulate]
  | succ n ih => simp [tabulate, OptimalLazyFinger.tabulate, ih]

@[simp] theorem optimize_ret (w : Nat → Nat → Computation Nat) (n : Nat) :
    (optimize w n).ret = OptimalLazyFinger.optimize (fun a b => (w a b).ret) n := by
  simp [optimize, OptimalLazyFinger.optimize]

/-- Erasing the counter recovers the already verified executable constructor. -/
@[simp] theorem treeFrom_ret (n p : Nat) (xs : List Nat) :
    (treeFrom n p xs).ret = OptimalLazyFinger.treeFrom n p xs := by
  simp [treeFrom, OptimalLazyFinger.treeFrom]

@[simp] theorem tree_ret (n : Nat) (xs : List Nat) :
    (tree n xs).ret = OptimalLazyFinger.tree n xs := treeFrom_ret _ _ _

end RotationBST.OptimalLazyFinger.Work
