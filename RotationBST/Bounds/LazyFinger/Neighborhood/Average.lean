module

public import RotationBST.Bounds.LazyFinger.Neighborhood.Counting
public import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Counting the nearby keys gives a lower bound for the sum of distances from
any fixed existing key. The additive term records the entire near ball. -/
theorem distance_sum_lower (t : Tree) (x r : Nat) (valid : x < t.size) :
    (r + 1) * t.size ≤ (r + 1) * 7 ^ r + ∑ y ∈ Finset.range t.size, distance t x y := by
  have pointwise : ∀ y ∈ Finset.range t.size,
      r + 1 ≤ (if distance t x y ≤ r then r + 1 else 0) + distance t x y := by
    intro y _
    split_ifs <;> omega
  have sum := Finset.sum_le_sum pointwise
  have near : (∑ y ∈ Finset.range t.size, if distance t x y ≤ r then r + 1 else 0) =
      (r + 1) * (ball t x r).card := by
    rw [← Finset.sum_filter]
    simp only [ball, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, near] at sum
  have bound := Nat.mul_le_mul_left (r + 1) (ball_card t x r valid)
  nlinarith

/-- If the universe is at least twice the radius-`r` counting bound, the average
distance from every existing key is at least `(r+1)/2`. -/
theorem average_distance_lower (t : Tree) (x r : Nat) (valid : x < t.size)
    (large : 2 * 7 ^ r ≤ t.size) :
    (r + 1) * t.size ≤ 2 * ∑ y ∈ Finset.range t.size, distance t x y := by
  have sum := distance_sum_lower t x r valid
  have scale := Nat.mul_le_mul_left (r + 1) large
  nlinarith

/-- Uniform all-pairs lower bound, independent of reference-tree shape. In a
universe of size at least `2 * 7^r`, random independent endpoints have average
distance at least `(r+1)/2`. This is the average-distance ingredient in the
strict lazy-finger/dynamic separation of arXiv:1304.6897, Theorem 6. -/
theorem pair_distance_lower (t : Tree) (r : Nat) (large : 2 * 7 ^ r ≤ t.size) :
    (r + 1) * t.size * t.size ≤
      2 * ∑ x ∈ Finset.range t.size, ∑ y ∈ Finset.range t.size, distance t x y := by
  have sum := Finset.sum_le_sum (fun x hx =>
    average_distance_lower t x r (Finset.mem_range.mp hx) large)
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum,
    Nat.mul_left_comm, Nat.mul_comm, Nat.mul_assoc] using sum

end RotationBST.LazyFinger
