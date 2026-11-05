module

public import RotationBST.Algorithms.OptimalLazyFinger.Preprocessing.Histogram
public import RotationBST.Bounds.LazyFinger.Frequencies.Proofs
public import RotationBST.Structures.PrefixSum.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.OptimalLazyFinger.Preprocessing
open PrefixSum LazyFinger

/-- The cached boundary query equals the direct sequence crossing count. -/
theorem toll_prepare (n p : Nat) (xs : List Nat) (hp : p < n)
    (valid : ∀ x ∈ xs, x < n) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ n) :
    toll (prepare n p xs) n lo hi = crossings lo hi p xs := by
  unfold prepare toll
  rw [rectangle_build _ n n lo hi 0 lo hlo hhi (Nat.zero_le _) (by omega),
    rectangle_build _ n n lo hi hi n hlo hhi hhi le_rfl,
    rectangle_build _ n n 0 lo lo hi (Nat.zero_le _) (by omega) hlo hhi,
    rectangle_build _ n n hi n lo hi hhi le_rfl hlo hhi,
    ← frequencyToll_rectangles n _ lo hi hlo hhi]
  have he : frequencyToll n (get (frequencies n p xs)) lo hi =
      frequencyToll n (frequency p xs) lo hi := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [get_frequencies n p xs a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)]
  rw [he, frequencyToll_eq_crossings n p xs hp valid]

end RotationBST.OptimalLazyFinger.Preprocessing
