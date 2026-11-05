module

public import RotationBST.Bounds.LazyFinger.Sequential.Scanning
public import RotationBST.Bounds.LazyFinger.Sequential.Entropy
public import RotationBST.Bounds.LazyFinger.Optimal
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem optimal_scans (n rounds : Nat) : optimalCost n (scans n rounds) ≤ 4 * rounds * n := by
  obtain ⟨t, ht, hc⟩ := optimalCost_attained n (scans n rounds)
  have h := scans_cost t rounds
  rw [ht, hc] at h
  exact h

/-- Explicit strict separation: increasing the universe yields any prescribed
factor, for every positive number of scans and every choice of the two shapes. -/
theorem scans_separate (C rounds : Nat) (hr : 0 < rounds) (lazy root : Tree)
    (hl : lazy.size = 2 ^ (12 * C)) (ht : root.size = 2 ^ (12 * C)) :
    C * cost lazy (scans (2 ^ (12 * C)) rounds) <
      StaticTree.cost root (scans (2 ^ (12 * C)) rounds) := by
  have hL := scans_cost lazy rounds
  rw [hl] at hL
  have hR := scans_root_power_lower root (12 * C) rounds ht
  rw [ht] at hR
  have hm : 0 < rounds * 2 ^ (12 * C) := Nat.mul_pos hr (by positivity)
  have hs := Nat.mul_le_mul_left C hL
  nlinarith

theorem optimal_scans_separate (C rounds : Nat) (hr : 0 < rounds) (root : Tree)
    (ht : root.size = 2 ^ (12 * C)) :
    C * optimalCost (2 ^ (12 * C)) (scans (2 ^ (12 * C)) rounds) <
      StaticTree.cost root (scans (2 ^ (12 * C)) rounds) := by
  have hL := optimal_scans (2 ^ (12 * C)) rounds
  have hR := scans_root_power_lower root (12 * C) rounds ht
  rw [ht] at hR
  have hm : 0 < rounds * 2 ^ (12 * C) := Nat.mul_pos hr (by positivity)
  have hs := Nat.mul_le_mul_left C hL
  nlinarith

/-- There is no uniform constant comparing best root-finger cost to best
lazy-finger cost. The witnesses are valid sequences at least as long as their
nonempty universes, so this gap is not an initialization artifact. -/
theorem root_lazy_unbounded (C : Nat) :
    ∃ n xs, 0 < n ∧ xs.length = n ∧ (∀ x ∈ xs, x < n) ∧
      ∀ t : Tree, t.size = n → C * optimalCost n xs < StaticTree.cost t xs := by
  refine ⟨2 ^ (12 * C), scans (2 ^ (12 * C)) 1, by positivity, ?_, scans_valid _ _, ?_⟩
  · simp
  · intro t ht
    exact optimal_scans_separate C 1 (by omega) t ht

/-- The separation survives any universe-dependent one-time allowance: repeat
scans long enough to make the gap exceed that allowance. -/
theorem root_lazy_unbounded_with_startup (C : Nat) (allowance : Nat → Nat) :
    ∃ n xs, 0 < n ∧ n ≤ xs.length ∧ (∀ x ∈ xs, x < n) ∧
      ∀ t : Tree, t.size = n → C * optimalCost n xs + allowance n < StaticTree.cost t xs := by
  let n := 2 ^ (12 * C)
  let rounds := 3 * allowance n + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hr : 0 < rounds := by dsimp [rounds]; omega
  refine ⟨n, scans n rounds, hn, ?_, scans_valid _ _, ?_⟩
  · rw [scans_length]
    nlinarith
  · intro t ht
    have hL := optimal_scans n rounds
    have hR := scans_root_power_lower t (12 * C) rounds ht
    rw [ht] at hR
    have hs := Nat.mul_le_mul_left C hL
    have hm : 3 * allowance n < rounds * n := by dsimp [rounds]; nlinarith
    change (12 * C + 1) * (rounds * n) ≤ _ at hR
    nlinarith

end RotationBST.LazyFinger
