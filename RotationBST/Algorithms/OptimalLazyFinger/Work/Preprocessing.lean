module

public import RotationBST.Algorithms.OptimalLazyFinger.Work.Erasure
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Work
open Cslib.Algorithms.Lean

@[simp] theorem fill_time (t : PrefixSum.Table) (p : Nat) (xs : List Nat) :
    (fill t p xs).time = 4 * xs.length + 1 := by
  induction xs generalizing t p with
  | nil => rfl
  | cons x xs ih => simp [fill, increment, ih]; omega

theorem frequencies_time (n p : Nat) (xs : List Nat) :
    (frequencies n p xs).time ≤ n * (n + 4) + 4 * xs.length + 4 := by
  have h := arrayOfFn_time_le n (fun _ => replicate n 0) (n + 1) (by intro i; rfl)
  simp only [frequencies, TimeM.time_bind, fill_time]
  nlinarith

theorem row_time (f : Nat → Computation Nat) (n C : Nat) (hf : ∀ i, (f i).time ≤ C) :
    (row f n).time ≤ n * (C + 4) + 1 := by
  induction n with
  | zero => simp [row]
  | succ n ih =>
    have h := hf n
    simp only [row, TimeM.time_bind, charge_time]
    nlinarith

theorem build_time (f : Nat → Nat → Computation Nat) (width height C : Nat)
    (hf : ∀ a b, (f a b).time ≤ C) :
    (build f width height).time ≤ height * (width * (C + 11) + 13) + width + 3 := by
  induction height with
  | zero => simp [build]
  | succ height ih =>
    have hr := row_time (f height) width C (hf height)
    have ha := arrayOfFn_time_le (width + 1)
      (fun b : Fin (width + 1) => charge 4
        (PrefixSum.get (build f width height).ret height b.val +
          (row (f height) width).ret[b.val]?.getD 0)) 4 (by intro b; rfl)
    simp only [build, TimeM.time_bind, charge_time]
    nlinarith

/-- One transition update per request, followed by quadratic prefix construction. -/
theorem prepare_time (n p : Nat) (xs : List Nat) :
    (prepare n p xs).time ≤ 4 * xs.length + 14 * n ^ 2 + 18 * n + 7 := by
  have hf := frequencies_time n p xs
  have hb := build_time (matrixGet (frequencies n p xs).ret) n n 2 (by intros; rfl)
  simp only [prepare, TimeM.time_bind]
  nlinarith

@[simp] theorem toll_time (p : PrefixSum.Table) (n lo hi : Nat) : (toll p n lo hi).time = 47 := rfl

end RotationBST.OptimalLazyFinger.Work
