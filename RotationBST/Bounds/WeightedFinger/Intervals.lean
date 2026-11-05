module

public import RotationBST.Bounds.WeightedFinger.Proofs

@[expose] public section
namespace RotationBST.WeightedFinger

theorem charge_congr {w v : Nat → ℝ} {x y : Nat}
    (h : ∀ k ∈ Finset.Icc (min x y) (max x y), w k = v k) :
    charge w x y = charge v x y := by
  have hx := h x (Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩)
  have hy := h y (Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩)
  have hm : mass w x y = mass v x y := Finset.sum_congr rfl h
  simp only [charge, hm, hx, hy]

/-- Translation of inorder ranks preserves inclusive interval mass. -/
theorem mass_shift (w : Nat → ℝ) (a x y : Nat) :
    mass (fun k => w (a + k)) x y = mass w (a + x) (a + y) := by
  unfold mass
  apply Finset.sum_bij (fun k _ => a + k)
  · intro k hk
    simp only [Finset.mem_Icc] at *
    omega
  · intro k hk j hj he
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - a, ?_, ?_⟩
    · simp only [Finset.mem_Icc]; omega
    · omega
  · intros; rfl

theorem charge_shift (w : Nat → ℝ) (a x y : Nat) :
    charge (fun k => w (a + k)) x y = charge w (a + x) (a + y) := by
  simp only [charge, mass_shift]

end RotationBST.WeightedFinger
