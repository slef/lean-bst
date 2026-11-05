module

public import RotationBST.Bounds.LazyFinger.Frequencies.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem frequencyToll_add (n : Nat) (f g : Nat → Nat → Nat) (lo hi : Nat) :
    frequencyToll n (fun a b => f a b + g a b) lo hi =
      frequencyToll n f lo hi + frequencyToll n g lo hi := by
  simp [frequencyToll, Nat.add_mul, Finset.sum_add_distrib]

theorem frequencyToll_single (n p x lo hi : Nat) (hp : p < n) (hx : x < n) :
    frequencyToll n (fun a b => if a = p ∧ b = x then 1 else 0) lo hi = cut lo hi p x := by
  simp [frequencyToll, ite_and, ite_mul, Finset.sum_ite_irrel, hp, hx]

/-- Pairwise frequencies preserve all interval-boundary crossing counts. -/
theorem frequencyToll_eq_crossings (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) :
    frequencyToll n (frequency p xs) lo hi = crossings lo hi p xs := by
  induction xs generalizing p with
  | nil => simp [frequencyToll, frequency, crossings]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have hv : ∀ y ∈ xs, y < n := fun y hy => valid y (by simp [hy])
    change frequencyToll n (fun a b => (if a = p ∧ b = x then 1 else 0) + frequency x xs a b) lo hi = _
    rw [frequencyToll_add, frequencyToll_single _ _ _ _ _ hp hx, ih x hx hv]
    rfl

private theorem restrict_range (n lo hi : Nat) (hhi : hi ≤ n) (g : Nat → Nat) :
    (∑ i ∈ Finset.range n, if lo ≤ i ∧ i < hi then g i else 0) = ∑ i ∈ Finset.Ico lo hi, g i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

private theorem restrict_rectangle (n a b c d : Nat) (hb : b ≤ n) (hd : d ≤ n)
    (f : Nat → Nat → Nat) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      if a ≤ i ∧ i < b then if c ≤ j ∧ j < d then f i j else 0 else 0) =
      ∑ i ∈ Finset.Ico a b, ∑ j ∈ Finset.Ico c d, f i j := by
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [restrict_range n a b hb]
  exact Finset.sum_congr rfl (fun i _ => restrict_range n c d hd (f i))

/-- Four rectangles count traffic in both directions between the interval and
its complement. No symmetry assumption on the directed frequency matrix is used. -/
theorem frequencyToll_rectangles (n : Nat) (f : Nat → Nat → Nat) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    frequencyToll n f lo hi =
      (∑ a ∈ Finset.Ico lo hi, ∑ b ∈ Finset.Ico 0 lo, f a b) +
      (∑ a ∈ Finset.Ico lo hi, ∑ b ∈ Finset.Ico hi n, f a b) +
      (∑ a ∈ Finset.Ico 0 lo, ∑ b ∈ Finset.Ico lo hi, f a b) +
      (∑ a ∈ Finset.Ico hi n, ∑ b ∈ Finset.Ico lo hi, f a b) := by
  have term (a b : Nat) (ha : a < n) (hb : b < n) : f a b * cut lo hi a b =
      (if lo ≤ a ∧ a < hi then if 0 ≤ b ∧ b < lo then f a b else 0 else 0) +
      (if lo ≤ a ∧ a < hi then if hi ≤ b ∧ b < n then f a b else 0 else 0) +
      (if 0 ≤ a ∧ a < lo then if lo ≤ b ∧ b < hi then f a b else 0 else 0) +
      (if hi ≤ a ∧ a < n then if lo ≤ b ∧ b < hi then f a b else 0 else 0) := by
    unfold cut
    split_ifs <;> omega
  unfold frequencyToll
  have hsum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun a ha =>
    Finset.sum_congr (s₁ := Finset.range n) rfl (fun b hb =>
      term a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)))
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  rw [restrict_rectangle n lo hi 0 lo hhi (by omega),
    restrict_rectangle n lo hi hi n hhi le_rfl,
    restrict_rectangle n 0 lo lo hi (by omega) hhi,
    restrict_rectangle n hi n lo hi le_rfl hhi]

end RotationBST.LazyFinger
