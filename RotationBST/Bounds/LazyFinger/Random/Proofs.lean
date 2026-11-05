module

public import RotationBST.Bounds.LazyFinger.AncestorDistance
public import RotationBST.Structures.Treap.Random.Common

@[expose] public section
namespace RotationBST.LazyFinger
open Treap.Random

/-- Exact expected movement cost in a weighted random treap. The negative
common-ancestor term is essential: dropping it yields a root-finger estimate
that depends on keys outside the interval between the requested endpoints. -/
theorem exists_expected_distance (w : Nat → ℝ) (n lo : Nat)
    (hw : ∀ k ∈ Finset.Ico lo (lo + n), 0 < w k) :
    ∃ T : List Nat → Tree, (∀ xs, (T xs).size = n) ∧
      ∀ x y, lo ≤ x → x < lo + n → lo ≤ y → y < lo + n →
        average w (Finset.Ico lo (lo + n)) (fun xs => (distance (T xs) (x - lo) (y - lo) : ℝ)) =
        ∑ a ∈ Finset.Ico lo (lo + n),
          (w a / (∑ k ∈ Finset.Icc (min a x) (max a x), w k) +
           w a / (∑ k ∈ Finset.Icc (min a y) (max a y), w k) -
           2 * (w a / (∑ k ∈ Finset.Icc (min a (min x y)) (max a (max x y)), w k))) := by
  obtain ⟨T, spec, prob⟩ := exists_random_treap w n lo hw
  refine ⟨T, fun xs => (spec xs).1, ?_⟩
  intro x y hx hx' hy hy'
  calc
    _ = average w (Finset.Ico lo (lo + n)) (fun xs =>
        ∑ a ∈ Finset.Ico lo (lo + n),
          ((if a ∈ (T xs).searchPath lo x then (1 : ℝ) else 0) +
           (if a ∈ (T xs).searchPath lo y then (1 : ℝ) else 0) -
           2 * (if a ∈ (T xs).searchPath lo x ∧ a ∈ (T xs).searchPath lo y then (1 : ℝ) else 0))) := by
      apply average_congr _ _ _ _ hw
      intro xs _
      have hxT : lo ≤ x ∧ x < lo + (T xs).size := by rw [(spec xs).1]; exact ⟨hx, hx'⟩
      have hyT : lo ≤ y ∧ y < lo + (T xs).size := by rw [(spec xs).1]; exact ⟨hy, hy'⟩
      simpa only [(spec xs).1] using distance_ancestor_sum (T xs) lo x y hxT hyT
    _ = _ := by
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_Ico.mp ha
      rw [average_sub, average_add, average_mul,
        prob a x ha'.1 ha'.2 hx hx', prob a y ha'.1 ha'.2 hy hy',
        common_ancestor_probability w n lo hw T spec a x y ha' ⟨hx, hx'⟩ ⟨hy, hy'⟩]

end RotationBST.LazyFinger
