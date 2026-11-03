module

public import RotationBST.Bounds.WorkingSet.Abstract

@[expose] public section

namespace RotationBST.BoundsBridge

theorem length_le_workingSetSum (n : Nat) (past xs : List Nat) :
    xs.length ≤ workingSetSum n past xs := by
  induction xs generalizing past with
  | nil => simp [workingSetSum]
  | cons x xs ih =>
      have := ih (past ++ [x])
      simp only [workingSetSum, List.length_cons]
      omega

theorem normalized_workingSet_iff (a : Algorithm) :
    HasWorkingSetBound a ↔
      ∃ C D : Nat, ∀ t xs, (∀ x ∈ xs, x < t.size) →
        a.totalCost t xs ≤ C * workingSetSum t.size [] xs +
          D * t.size * (1 + t.size.log2) := by
  constructor
  · rintro ⟨C, D, h⟩
    refine ⟨C + 1, D, ?_⟩
    intro t xs hv
    have hc := h t xs hv
    have hl := length_le_workingSetSum t.size [] xs
    simp only [Algorithm.totalCost, Nat.add_mul, Nat.one_mul]
    omega
  · rintro ⟨C, D, h⟩
    refine ⟨C, D, ?_⟩
    intro t xs hv
    have := h t xs hv
    unfold Algorithm.totalCost at this
    omega

theorem total_dynamic (a : Algorithm) (h : DynamicallyOptimal a) :
    TotallyDynamicallyOptimal a := by
  obtain ⟨C, D, h⟩ := h
  refine ⟨C + 1, D, ?_⟩
  intro t xs u k he
  have := h t xs u k he
  simp only [Algorithm.totalCost, Nat.add_mul, Nat.mul_add, Nat.one_mul]
  omega

end RotationBST.BoundsBridge
