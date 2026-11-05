module

public import RotationBST.Bounds.LazyFinger.Sequential.Separation
public import RotationBST.Bounds.LazyFinger.Diagonal
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.LazyFinger

theorem scanPrefix_length (n m : Nat) : (scanPrefix n m).length = m := by
  simp only [scanPrefix, List.length_append, scans_length, List.length_range]
  have h := Nat.mod_add_div m n
  nlinarith

theorem scanPrefix_valid (n m : Nat) (positive : 0 < n) : ∀ x ∈ scanPrefix n m, x < n := by
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact scans_valid n (m / n) x member
  · have smaller := List.mem_range.mp member
    have remainder := Nat.mod_lt m positive
    omega

theorem scanPrefix_crossings (lo hi p n m : Nat) :
    crossings lo hi p (scanPrefix n m) ≤ 3 * (m / n + 1) := by
  rw [scanPrefix, crossings_append]
  have first := crossings_scans lo hi p n (m / n)
  have last := crossings_range lo hi ((scans n (m / n)).getLastD p) (m % n)
  omega

/-- A partial final scan contributes at most three crossings per edge.
Once one full scan fits, this is absorbed into a uniform linear charge. -/
theorem scanPrefix_costFrom (t : Tree) (p m : Nat) (hp : p < t.size) (long : t.size ≤ m) :
    costFrom t p (scanPrefix t.size m) ≤ 8 * (m / t.size) * t.size := by
  have positive : 0 < t.size := by omega
  rw [costFrom_eq_crossings t p _ hp (scanPrefix_valid t.size m positive), scanPrefix_length t.size m]
  have bound := intervalCost_le_size (fun a b => crossings a b p (scanPrefix t.size m)) (3 * (m / t.size + 1))
    (fun a b => scanPrefix_crossings a b p t.size m) t 0
  have remainder := Nat.mod_lt m positive
  have split := Nat.mod_add_div m t.size
  have rounds : 1 ≤ m / t.size := (Nat.le_div_iff_mul_le positive).mpr (by simpa using long)
  have enough := Nat.mul_le_mul_right t.size rounds
  nlinarith

theorem scanPrefix_cost (t : Tree) (m : Nat) (positive : 0 < t.size) (long : t.size ≤ m) :
    cost t (scanPrefix t.size m) ≤ 8 * (m / t.size) * t.size := by
  cases t with
  | nil => simp [Tree.size] at positive
  | node l r => exact scanPrefix_costFrom (.node l r) l.size m (by simp [Tree.size]; omega) long

theorem scanPrefix_root (t : Tree) (h m : Nat) (size : t.size = 2 ^ h) :
    (h + 1) * ((m / t.size) * t.size) ≤ 3 * StaticTree.cost t (scanPrefix t.size m) := by
  have lower := scans_root_power_lower t h (m / t.size) size
  have monotone : StaticTree.cost t (scans t.size (m / t.size)) ≤ StaticTree.cost t (scanPrefix t.size m) := by
    simp only [scanPrefix, StaticTree.cost, List.map_append, List.sum_append]
    omega
  exact lower.trans (Nat.mul_le_mul_left 3 monotone)

/-- Every sufficiently long prescribed length supports a shape-uniform gap,
even after any universe-dependent startup allowance. -/
theorem root_lazy_all_lengths (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ lazy root : Tree, lazy.size = n → root.size = n →
          C * cost lazy xs + allowance n < StaticTree.cost root xs := by
  let n := 2 ^ (24 * C)
  let threshold := (3 * allowance n + 1) * n
  have positive : 0 < n := by dsimp [n]; positivity
  have thresholdLarge : n ≤ threshold := by dsimp [threshold]; nlinarith
  refine ⟨n, threshold, positive, thresholdLarge, ?_⟩
  intro m long
  have enough : n ≤ m := thresholdLarge.trans long
  refine ⟨scanPrefix n m, scanPrefix_length n m, scanPrefix_valid n m positive, ?_⟩
  intro lazy root lazySize rootSize
  have upper := scanPrefix_cost lazy m (by omega) (by omega)
  rw [lazySize] at upper
  have lower := scanPrefix_root root (24 * C) m rootSize
  rw [rootSize] at lower
  have rounds : 3 * allowance n + 1 ≤ m / n := (Nat.le_div_iff_mul_le positive).mpr long
  have bulk : 3 * allowance n < (m / n) * n := by nlinarith
  have paid := Nat.mul_le_mul_left C upper
  change (24 * C + 1) * ((m / n) * n) ≤ _ at lower
  nlinarith

/-- The same eventual all-length gap against the optimal lazy-finger tree. -/
theorem optimal_root_lazy_all_lengths (C : Nat) (allowance : Nat → Nat) :
    ∃ n threshold, 0 < n ∧ n ≤ threshold ∧ ∀ m, threshold ≤ m →
      ∃ xs, xs.length = m ∧ (∀ x ∈ xs, x < n) ∧
        ∀ root : Tree, root.size = n →
          C * optimalCost n xs + allowance n < StaticTree.cost root xs := by
  obtain ⟨n, threshold, positive, large, allLengths⟩ := root_lazy_all_lengths C allowance
  refine ⟨n, threshold, positive, large, ?_⟩
  intro m long
  obtain ⟨xs, length, valid, gap⟩ := allLengths m long
  obtain ⟨lazy, size, optimal⟩ := optimalCost_attained n xs
  exact ⟨xs, length, valid, fun root rootSize => by simpa only [optimal] using gap lazy root size rootSize⟩

/-- A single family, indexed only by sequence length, eventually defeats
every fixed factor. This makes the little-omega quantifier order explicit. -/
theorem optimal_root_lazy_family (allowance : Nat → Nat) :
    ∃ sizes : Nat → Nat, ∃ family : Nat → List Nat,
      (∀ m, 0 < sizes m ∧ (family m).length = m ∧
        (∀ x ∈ family m, x < sizes m)) ∧
      ∀ C, ∃ threshold, ∀ m, threshold ≤ m →
        ∀ root : Tree, root.size = sizes m →
          C * optimalCost (sizes m) (family m) + allowance (sizes m) <
            StaticTree.cost root (family m) := by
  apply sequence_family_of_eventual_witnesses
    (fun C n xs => ∀ root : Tree, root.size = n →
      C * optimalCost n xs + allowance n < StaticTree.cost root xs)
  · intro a b n xs factor gap root size
    exact (Nat.add_le_add_right (Nat.mul_le_mul_right (optimalCost n xs) factor) _).trans_lt (gap root size)
  · intro C
    obtain ⟨n, threshold, positive, _, witnesses⟩ := optimal_root_lazy_all_lengths C allowance
    exact ⟨n, threshold, positive, witnesses⟩

end RotationBST.LazyFinger
