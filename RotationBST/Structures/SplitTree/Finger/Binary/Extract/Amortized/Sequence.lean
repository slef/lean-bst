module

public import RotationBST.Structures.SplitTree.Finger.Binary.Extract.Amortized.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Telescoping the concrete extraction potential gives constant amortized cost. -/
theorem extractMany_credit (n : Nat) {h : Nat} {t : Multiway} (valid : Balanced h t) :
    ∃ k, Balanced k (extractMany n t).1 ∧
      (extractMany n t).2 + storedCredit true (extractMany n t).1 ≤ storedCredit true t + 3 * n := by
  induction n generalizing h t with
  | zero => exact ⟨h, valid, by simp [extractMany]⟩
  | succ n ih =>
    have balance := (extractMinAux_balance (t.nodes + 1) valid (by omega)).1
    have step : (extractView t).2 + storedCredit true (extractView t).1 ≤ storedCredit true t + 3 :=
      (extractFingerAux_credit _ valid (by omega) true).2
    have next : ∃ k, Balanced k (extractView t).1 := by
      rcases balance with same | ⟨k, _, smaller⟩
      · exact ⟨h, same⟩
      · exact ⟨k, smaller⟩
    obtain ⟨k, next⟩ := next
    obtain ⟨j, finalBalance, total⟩ := ih next
    refine ⟨j, finalBalance, ?_⟩
    simp only [extractMany]
    omega

theorem extractMany_cost (n : Nat) {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (extractMany n t).2 ≤ 12 * t.nodes + 3 * n := by
  obtain ⟨_, _, total⟩ := extractMany_credit n valid
  have reserve := repairCredit_bound valid true
  rw [← storedCredit_eq valid true] at reserve
  omega

theorem extractMany_size (n : Nat) (t : Multiway) : (extractMany n t).1.size = t.size - n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    have step : (extractView t).1.size = t.size - 1 := by
      by_cases empty : t = .nil
      · subst t; rfl
      · have drop := extractMin_size t empty
        change (extractMin t).1.size = t.size - 1
        omega
    simp only [extractMany]
    rw [ih, step]
    omega

theorem extractMany_empty (t : Multiway) : (extractMany t.size t).1 = .nil := by
  have empty := extractMany_size t.size t
  cases result : (extractMany t.size t).1 <;> simp_all [size]

end RotationBST.Geometric.Split.Multiway.Finger
