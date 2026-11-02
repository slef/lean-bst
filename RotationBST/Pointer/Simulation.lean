module

public import RotationBST.Pointer.Basic

@[expose] public section

namespace RotationBST.Pointer

variable {s t u : Tree} {xs : List Nat} {i k : Nat}

/-- Charge pending rotations to the next request, or retain them as a final
suffix when there are no requests left. -/
private theorem prepend_pending (hr : Rotations s t i)
    (he : RotationBST.Execution t xs u k) :
    ∃ v p q, RotationBST.Execution s xs v p ∧ Rotations v u q ∧ p + q = i + k := by
  cases he with
  | nil => exact ⟨s, 0, i, .nil, hr, by omega⟩
  | @cons t v x a xs u b ha hb =>
      exact ⟨u, i + a + b, 0, .cons ⟨hr.append ha.1, ha.2⟩ hb,
        .refl, by omega⟩

/-- A conventional pointer execution admits a root-access rotation execution
with at most a factor three in total cost. Any outstanding final restructuring
is retained explicitly as a suffix and included in the bound. -/
theorem execution_to_rotations (h : Execution s xs t k) :
    ∃ u r q, RotationBST.Execution s xs u r ∧ Rotations u t q ∧
      xs.length + r + q ≤ 3 * k := by
  induction h with
  | nil => exact ⟨_, 0, 0, .nil, .refl, by simp⟩
  | @cons s t x k xs u m ha _ ih =>
      obtain ⟨v, p, q, hv, hq, hk⟩ := serves_split ha
      obtain ⟨w, a, b, hw, hb, hm⟩ := ih
      obtain ⟨z, c, d, hz, hd, heq⟩ := prepend_pending hq hw
      refine ⟨z, p + c, d + b, .cons hv hz, hd.append hb, ?_⟩
      simp only [List.length_cons]
      omega

end RotationBST.Pointer
