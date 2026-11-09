module

public import RotationBST.Algorithms.Tango.Algorithm.BottomUp.Linear
public import RotationBST.Algorithms.Tango.Algorithm.Rotation.Proofs
public import RotationBST.Algorithms.Tango.Reference.Bounds
public import RotationBST.Models.Rotation.Existence.Proofs
import Mathlib.Tactic

@[expose] public section

/-! Tango with linear startup as one online algorithm: the bottom-up policy on
the balanced reference tree, erased to a rotation algorithm. From another
initial tree the erasure pays one reset of at most `2n` rotations. -/
namespace RotationBST.Tango

theorem exists_online_linear_bound (n : Nat) :
    ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      start.size = n → Execution start xs finish offline →
        (A.totalCost start xs : ℝ) ≤
          (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) + 44 * n := by
  obtain ⟨p, _steps, bound⟩ := BottomUp.balanced_policy n
  obtain ⟨a, _exact, reset⟩ := p.rotation_algorithm
  refine ⟨a, ?_⟩
  intro start finish xs offline size execution
  have same : start.size = (balanced n).size := size.trans (balanced_size n).symm
  have valid : ∀ x ∈ xs, x < (balanced n).size := by
    intro x hx; rw [← same]; exact AccessBridge.execution_valid execution x hx
  have hr := reset start same xs valid
  have hb := bound start finish xs offline size execution
  rw [size] at hr
  have cast : (a.totalCost start xs : ℝ) ≤ xs.length + (p.run xs).2 + 2 * n := by
    exact_mod_cast hr
  linarith

end RotationBST.Tango
