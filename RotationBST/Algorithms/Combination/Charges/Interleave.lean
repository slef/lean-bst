module

public import RotationBST.Algorithms.Combination.Charges.Definitions.Abstract
public import RotationBST.Bounds.Interleave.Superadditive
public import RotationBST.Bounds.Interleave.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Charges

private theorem prefix_mono (t : Tree) (xs : List Nat) (lo hi : Nat) (ordered : lo ≤ hi) :
    Wilber.interleave t (xs.take lo) ≤ Wilber.interleave t (xs.take hi) := by
  have split : xs.take hi = xs.take lo ++ (xs.drop lo).take (hi - lo) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.take_add (l := xs) (i := lo) (j := hi - lo))
  rw [split]
  have bound := Wilber.interleave_superadditive t (xs.take lo) ((xs.drop lo).take (hi - lo))
  omega

theorem interleave_nonneg (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) :
    0 ≤ interleave factor t xs i := by
  apply mul_nonneg (Nat.cast_nonneg _)
  have bound : (Wilber.interleave t (xs.take i) : ℝ) ≤ Wilber.interleave t (xs.take (i + 1)) :=
    Nat.cast_le.mpr (prefix_mono t xs i (i + 1) (by omega))
  linarith

theorem interleave_mass (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.mass (fun _ => interleave factor t) side xs lo hi =
      factor * ((hi - lo : Nat) + (Wilber.interleave t (xs.take hi) : ℝ) - Wilber.interleave t (xs.take lo)) := by
  induction hi, ordered using Nat.le_induction with
  | base => simp [Analysis.mass]
  | succ hi ordered ih =>
    rw [Analysis.mass, Finset.sum_Ico_succ_top ordered]
    change Analysis.mass (fun _ => interleave factor t) side xs lo hi + interleave factor t xs hi = _
    rw [ih, interleave, Nat.succ_sub ordered, Nat.cast_succ]
    ring

theorem interleave_total (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat) :
    Analysis.total (fun _ => interleave factor t) side xs = factor * (xs.length + Wilber.interleave t xs : Nat) := by
  rw [Analysis.total, interleave_mass factor t side xs 0 xs.length (Nat.zero_le _)]
  simp [Wilber.interleave_nil, Nat.cast_add]

/-- No restart charge is needed for the benchmark itself: switches internal
 to a segment also occur in the original execution. -/
theorem interleave_stable (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.total (fun _ => interleave factor t) side (Analysis.segment xs lo hi) ≤
      Analysis.mass (fun _ => interleave factor t) side xs lo hi := by
  rw [interleave_total, interleave_mass factor t side xs lo hi ordered]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have split : xs.take hi = xs.take lo ++ (xs.drop lo).take (hi - lo) := by
    simpa only [Nat.add_sub_of_le ordered] using (List.take_add (l := xs) (i := lo) (j := hi - lo))
  have bound := Wilber.interleave_superadditive t (xs.take lo) (Analysis.segment xs lo hi)
  change xs.take hi = xs.take lo ++ Analysis.segment xs lo hi at split
  rw [← split] at bound
  have count : (Analysis.segment xs lo hi).length ≤ hi - lo := by simp [Analysis.segment]
  have realBound : (Wilber.interleave t (xs.take lo) : ℝ) + Wilber.interleave t (Analysis.segment xs lo hi) ≤
      Wilber.interleave t (xs.take hi) := by exact_mod_cast bound
  have realCount : ((Analysis.segment xs lo hi).length : ℝ) ≤ (hi - lo : Nat) := by exact_mod_cast count
  push_cast
  linarith

/-- These same charges compare against every offline execution, independently
of the source worker chosen to realize them. -/
theorem interleave_comparator (factor : Nat) (reference : Tree) {s t : Tree} {xs : List Nat} {k : Nat}
    (same : reference.size = s.size) (execution : RotationBST.Execution s xs t k) :
    Analysis.total (fun _ => interleave factor reference) false xs ≤
      (4 * factor : Nat) * (xs.length + k : Nat) := by
  rw [interleave_total]
  have bound := Wilber.Results.rotation_lower_bound reference same execution
  have result : factor * (xs.length + Wilber.interleave reference xs) ≤ 4 * factor * (xs.length + k) := by nlinarith
  exact_mod_cast result

end RotationBST.Combo.Charges
