module

public import RotationBST.Algorithms.Tango.Algorithm.Competitive
public import RotationBST.Algorithms.Tango.Reference.Bounds

@[expose] public section
namespace RotationBST.Tango

/-- For every key count, an explicit balanced reference gives a doubly
logarithmic competitive coefficient, with initialization charged separately. -/
theorem Policy.balanced_competitive_bound (n : Nat) (p : Policy (balanced n))
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : start.size = n) (execution : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 (Nat.log2 n + 1) + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 (Nat.log2 n + 1) + 4) * n := by
  have same : (balanced n).size = start.size := (balanced_size n).trans size.symm
  have bound := p.competitive_bound same execution
  rw [balanced_size] at bound
  have monotone := Splay.Updates.log_nat_mono (balanced_height n)
  have requests := mul_le_mul_of_nonneg_right monotone (Nat.cast_nonneg (offline + xs.length) (α := ℝ))
  have keys := mul_le_mul_of_nonneg_right monotone (Nat.cast_nonneg n (α := ℝ))
  simp only [Nat.cast_add, Nat.cast_one] at monotone requests keys
  nlinarith

end RotationBST.Tango
