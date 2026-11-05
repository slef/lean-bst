module

public import RotationBST.Bounds.WeightedFinger.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.WeightedFinger

theorem length_le_costFrom (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (hw : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (xs.length : ℝ) ≤ costFrom w p xs := by
  induction xs generalizing p with
  | nil => simp [costFrom]
  | cons x xs ih =>
    have hx := valid x (by simp)
    have hv : ∀ y ∈ xs, y < n := fun y hy => valid y (by simp [hy])
    have ht := ih x hx hv
    have hc := charge_ge_one w p x (by
      intro k hk
      apply hw k
      have := (Finset.mem_Icc.mp hk).2
      omega)
    simp only [costFrom, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

theorem costValues_nonempty (n p : Nat) (xs : List Nat) :
    {c | ∃ w : Nat → ℝ, (∀ k < n, 0 < w k) ∧ costFrom w p xs = c}.Nonempty :=
  ⟨costFrom (fun _ => 1) p xs, (fun _ => 1), (by intros; norm_num), rfl⟩

theorem costValues_bddBelow (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    BddBelow {c | ∃ w : Nat → ℝ, (∀ k < n, 0 < w k) ∧ costFrom w p xs = c} := by
  refine ⟨(xs.length : ℝ), ?_⟩
  rintro c ⟨w, hw, rfl⟩
  exact length_le_costFrom w n p xs hw hp valid

theorem optimalCostFrom_le (w : Nat → ℝ) (n p : Nat) (xs : List Nat)
    (hw : ∀ k < n, 0 < w k) (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    optimalCostFrom n p xs ≤ costFrom w p xs :=
  csInf_le (costValues_bddBelow n p xs hp valid) ⟨w, hw, rfl⟩

theorem le_optimalCostFrom (n p : Nat) (xs : List Nat) (b : ℝ)
    (h : ∀ w : Nat → ℝ, (∀ k < n, 0 < w k) → b ≤ costFrom w p xs) :
    b ≤ optimalCostFrom n p xs := by
  apply le_csInf (costValues_nonempty n p xs)
  rintro c ⟨w, hw, rfl⟩
  exact h w hw

theorem length_le_optimalCostFrom (n p : Nat) (xs : List Nat)
    (hp : p < n) (valid : ∀ x ∈ xs, x < n) :
    (xs.length : ℝ) ≤ optimalCostFrom n p xs :=
  le_optimalCostFrom n p xs _ (fun w hw => length_le_costFrom w n p xs hw hp valid)

end RotationBST.WeightedFinger
