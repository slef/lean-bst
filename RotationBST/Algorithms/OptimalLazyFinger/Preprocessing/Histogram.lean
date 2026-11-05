module

public import RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Preprocessing
open PrefixSum

theorem increment_square (t : Table) (n a b : Nat) (ht : Square t n) :
    Square (increment t a b) n := by
  refine ⟨by simpa [increment] using ht.1, ?_⟩
  intro i hi
  have hit : i < t.size := by rw [ht.1]; exact hi
  simp only [increment, Array.getElem?_modify]
  split
  · rw [Array.getElem?_eq_getElem hit]
    simp only [Option.map_some, Option.getD_some, Array.size_modify]
    simpa only [Array.getElem?_eq_getElem hit, Option.getD_some] using ht.2 i hi
  · exact ht.2 i hi

theorem get_increment (t : Table) (n a b i j : Nat) (ht : Square t n)
    (hi : i < n) (hj : j < n) :
    get (increment t a b) i j = get t i j + (if i = a ∧ j = b then 1 else 0) := by
  have hit : i < t.size := by rw [ht.1]; exact hi
  have hr : t[i].size = n := by
    simpa only [Array.getElem?_eq_getElem hit, Option.getD_some] using ht.2 i hi
  have hjr : j < t[i].size := by omega
  unfold increment PrefixSum.get
  rw [Array.getElem?_modify, Array.getElem?_eq_getElem hit]
  by_cases ha : a = i
  · subst a
    simp only [↓reduceIte, Option.map_some, Option.getD_some, Array.getElem?_modify,
      Array.getElem?_eq_getElem hjr]
    by_cases hb : b = j
    · subst b; simp
    · simp [hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]

theorem fill_square (t : Table) (n p : Nat) (xs : List Nat) (ht : Square t n) :
    Square (fill t p xs) n := by
  induction xs generalizing t p with
  | nil => exact ht
  | cons x xs ih => exact ih _ _ (increment_square t n p x ht)

/-- The array accumulator records exactly the mathematical pair frequencies. -/
theorem get_fill (t : Table) (n p : Nat) (xs : List Nat) (ht : Square t n)
    (i j : Nat) (hi : i < n) (hj : j < n) :
    get (fill t p xs) i j = get t i j + LazyFinger.frequency p xs i j := by
  induction xs generalizing t p with
  | nil => simp [fill, LazyFinger.frequency]
  | cons x xs ih =>
    rw [fill, ih _ _ (increment_square t n p x ht), get_increment t n p x i j ht hi hj]
    simp only [LazyFinger.frequency, Nat.add_assoc]

theorem zero_square (n : Nat) : Square (Array.replicate n (Array.replicate n 0)) n := by
  constructor
  · simp
  · intro i hi
    simp [hi]

theorem frequencies_square (n p : Nat) (xs : List Nat) : Square (frequencies n p xs) n :=
  fill_square _ n p xs (zero_square n)

theorem get_frequencies (n p : Nat) (xs : List Nat) (i j : Nat) (hi : i < n) (hj : j < n) :
    get (frequencies n p xs) i j = LazyFinger.frequency p xs i j := by
  rw [frequencies, get_fill _ n p xs (zero_square n) i j hi hj]
  simp [PrefixSum.get, hi, hj]

end RotationBST.OptimalLazyFinger.Preprocessing
