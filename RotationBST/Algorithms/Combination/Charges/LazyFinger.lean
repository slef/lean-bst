module

public import RotationBST.Algorithms.Combination.Charges.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Prefixes
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Charges

theorem lazyFinger_nonneg (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) :
    0 ≤ lazyFinger factor t xs i := by
  apply mul_nonneg (Nat.cast_nonneg _)
  exact sub_nonneg.mpr (Nat.cast_le.mpr (LazyFinger.cost_take_mono t xs i (i + 1) (by omega)))

/-- A window's charges are exactly its contribution to the original run. -/
theorem lazyFinger_mass (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.mass (fun _ => lazyFinger factor t) side xs lo hi =
      factor * ((LazyFinger.cost t (xs.take hi) : ℝ) - LazyFinger.cost t (xs.take lo)) := by
  induction hi, ordered using Nat.le_induction with
  | base => simp [Analysis.mass]
  | succ hi ordered ih =>
    rw [Analysis.mass, Finset.sum_Ico_succ_top ordered]
    change Analysis.mass (fun _ => lazyFinger factor t) side xs lo hi + lazyFinger factor t xs hi = _
    rw [ih, lazyFinger]
    ring

theorem lazyFinger_total (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat) :
    Analysis.total (fun _ => lazyFinger factor t) side xs = factor * LazyFinger.cost t xs := by
  rw [Analysis.total, lazyFinger_mass factor t side xs 0 xs.length (Nat.zero_le _)]
  have empty : LazyFinger.cost t [] = 0 := by cases t <;> rfl
  simp [empty]

/-- Restarting a segment needs only one linear initialization charge, uniformly
in the reference tree and in both worker sides. -/
theorem lazyFinger_stable (factor overhead : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) (valid : ∀ x ∈ xs, x < t.size)
    (paid : factor * t.size ≤ overhead) :
    Analysis.total (fun _ => lazyFinger factor t) side (Analysis.segment xs lo hi) + overhead ≤
      Analysis.mass (fun _ => lazyFinger factor t) side xs lo hi + 2 * overhead := by
  rw [lazyFinger_total, lazyFinger_mass factor t side xs lo hi ordered]
  have mono := LazyFinger.cost_take_mono t xs lo hi ordered
  have bound := LazyFinger.cost_segment t xs lo hi ordered valid
  have realBound : (LazyFinger.cost t (Analysis.segment xs lo hi) : ℝ) ≤
      (LazyFinger.cost t (xs.take hi) : ℝ) - LazyFinger.cost t (xs.take lo) + t.size := by
    exact_mod_cast (show LazyFinger.cost t (Analysis.segment xs lo hi) ≤
      LazyFinger.cost t (xs.take hi) - LazyFinger.cost t (xs.take lo) + t.size from bound)
  have scaled := mul_le_mul_of_nonneg_left realBound (Nat.cast_nonneg factor : (0 : ℝ) ≤ factor)
  have paidReal : (factor : ℝ) * t.size ≤ overhead := by exact_mod_cast paid
  nlinarith

end RotationBST.Combo.Charges
