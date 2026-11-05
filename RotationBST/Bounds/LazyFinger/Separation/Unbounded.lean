module

public import RotationBST.Bounds.LazyFinger.Separation.Dynamic

@[expose] public section
namespace RotationBST.LazyFinger

/-- Long pair blocks amortize all physical reshaping work into a constant
number of instructions per request, for any prescribed initial tree. -/
theorem pairSequence_dynamic_long (s : Tree) (rounds : Nat) (long : 16 * s.size ≤ rounds) :
    ∃ t k, t.size = s.size ∧ Pointer.Execution s (pairSequence s.size rounds) t k ∧
      k ≤ 7 * rounds * s.size * s.size := by
  obtain ⟨t, k, size, execution, bound⟩ := pairSequence_dynamic s rounds
  have scale := Nat.mul_le_mul_left (s.size * s.size) long
  exact ⟨t, k, size, execution, by nlinarith⟩

/-- Strict lazy-finger/dynamic separation. For any factor and any one-time
universe-dependent allowance, one valid sequence defeats that comparison.
Every prescribed dynamic initial shape has a legal cheap execution, whereas
the lower bound applies even to the best static lazy-finger tree chosen after
the sequence. The deterministic witnesses enumerate all two-key blocks. -/
theorem lazy_dynamic_unbounded_with_startup (C : Nat) (allowance : Nat → Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧
        C * k + allowance n < optimalCost n xs := by
  let r := 14 * C + 2
  let n := 2 * 7 ^ r
  let rounds := 16 * n + 2 * allowance n + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hr : 0 < rounds := by dsimp [rounds]; omega
  have long : 16 * n ≤ rounds := by dsimp [rounds]; omega
  have gap : 2 * allowance n < rounds * n * n := by
    have one : 1 ≤ n * n := by nlinarith
    have scale := Nat.mul_le_mul_left rounds one
    dsimp [rounds] at scale ⊢
    nlinarith
  refine ⟨n, pairSequence n rounds, hn, ?_, pairSequence_valid n rounds, ?_⟩
  · rw [pairSequence_length]
    have hnn : n ≤ n * n := by nlinarith
    have scale := Nat.mul_le_mul_right (n * n) (show 1 ≤ 2 * rounds by omega)
    nlinarith
  · intro s size
    obtain ⟨t, k, _, execution, upper⟩ := pairSequence_dynamic_long s rounds (by simpa only [size] using long)
    rw [size] at execution upper
    obtain ⟨reference, referenceSize, optimum⟩ := optimalCost_attained n (pairSequence n rounds)
    have lower := pairSequence_lower reference rounds r (by rw [referenceSize])
    rw [referenceSize, optimum] at lower
    have scale := Nat.mul_le_mul_left (2 * C) upper
    refine ⟨t, k, execution, ?_⟩
    dsimp [r] at lower
    nlinarith

/-- No uniform constant bounds optimal lazy finger by dynamic execution cost,
even for nonempty universes and sequences at least as long as their universes. -/
theorem lazy_dynamic_unbounded (C : Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ s : Tree, s.size = n → ∃ t k, Pointer.Execution s xs t k ∧ C * k < optimalCost n xs := by
  simpa only [Nat.add_zero] using lazy_dynamic_unbounded_with_startup C (fun _ => 0)

end RotationBST.LazyFinger
