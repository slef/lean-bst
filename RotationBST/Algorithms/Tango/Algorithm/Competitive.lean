module

public import RotationBST.Algorithms.Tango.Algorithm.Policy
public import RotationBST.Algorithms.Tango.Preferences.Updates.Comparison
public import RotationBST.Bounds.Interleave.Changes

@[expose] public section
namespace RotationBST.Tango

/-- The online policy costs logarithmically in reference height per preferred
path change, plus one final component access per request. -/
theorem Policy.interleave_bound {reference : Tree} (p : Policy reference) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < reference.size) :
    ((p.run xs).2 : ℝ) ≤
      (interleave reference xs + reference.size) * (14 * Real.logb 2 (height reference) + 4) +
        xs.length * (3 * Real.logb 2 (height reference) + 1) := by
  have bound := (p.run_spec xs valid).2.2
  have count : ((preferenceLog reference [] xs).length : ℝ) ≤
      (interleave reference xs + reference.size : Nat) := by
    exact_mod_cast preferenceLog_bound reference xs valid
  have positive := Bounds.logb_nat_nonneg (height reference)
  simp only [Nat.cast_add] at count
  nlinarith

/-- Conventional cost is one unit per request plus rotations. Comparison is
against every offline execution on the same key universe; initialization is
charged separately for each reference key. -/
theorem Policy.competitive_bound {reference : Tree} (p : Policy reference)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (execution : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 (height reference) + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 (height reference) + 4) * reference.size := by
  have valid : ∀ x ∈ xs, x < reference.size := by
    rw [size]
    exact AccessBridge.execution_valid execution
  have bound := (p.run_spec xs valid).2.2
  have count : ((preferenceLog reference [] xs).length : ℝ) ≤
      (4 * offline + 2 * xs.length + reference.size : Nat) := by
    exact_mod_cast preferenceLog_le_rotations reference size execution
  have positive := Bounds.logb_nat_nonneg (height reference)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at count ⊢
  nlinarith

/-- A perfect reference tree has `2^h - 1` keys, so its competitive factor is
logarithmic in `h`, equivalently doubly logarithmic in the universe size. -/
theorem Policy.perfect_competitive_bound (h : Nat) (p : Policy (perfect h))
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : (perfect h).size = start.size) (execution : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 h + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 h + 4) * (2 ^ h - 1 : Nat) := by
  simpa only [perfect_height, perfect_size] using p.competitive_bound size execution

end RotationBST.Tango
