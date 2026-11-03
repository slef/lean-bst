module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Lifetime.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

theorem split_intervalCredit {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) :
    (split state rank).cost + intervalCredit (split state rank).left + intervalCredit (split state rank).right ≤
      intervalCredit (some state) := by
  have cost := split_credit valid rank existsKey
  have sizes := split_sizes valid rank existsKey
  have accounting := charge_reserve rank (state.size - 1 - rank)
  have leftLog := totalCharge_reserve (intervalTree (split state rank).left)
  have rightLog := totalCharge_reserve (intervalTree (split state rank).right)
  have inputLog := totalCharge_reserve state.tree
  rw [sizes.1] at leftLog
  rw [sizes.2] at rightLog
  rw [state_size] at inputLog
  simp only [charge] at accounting
  simp only [intervalCredit]
  rw [sizes.1, sizes.2, show (intervalTree (some state)).size = state.size from state_size state]
  rw [show intervalNodes (some state) = (Fragment.shared state).nodes from rfl]
  have total : rank + (state.size - 1 - rank) + 2 = state.size + 1 := by omega
  rw [total] at accounting
  omega

theorem runPlan_budget (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    (runPlan plan input).2 + (runPlan plan input).1.credit ≤ intervalCredit input := by
  induction plan generalizing input with
  | stop => simp [runPlan, Partitioned.credit]
  | branch rank l r il ir =>
    cases input with
    | none => exact False.elim applicable
    | some state =>
      have good := split_valid valid rank applicable.1
      have left := il _ good.1 applicable.2.1
      have right := ir _ good.2 applicable.2.2
      have paid := split_intervalCredit valid rank applicable.1
      simp only [runPlan, Partitioned.credit]
      omega

theorem Refine.spec {s t : Partitioned} {cost : Nat} (step : Refine s t cost) (valid : s.Valid) :
    t.Valid ∧ Rotations s.tree t.tree cost ∧ cost + t.credit ≤ s.credit := by
  induction step with
  | leaf plan input applicable =>
    have result := runPlan_spec plan input valid applicable
    exact ⟨result.1, result.2, runPlan_budget plan input valid applicable⟩
  | left step ih =>
    have result := ih valid.1
    exact ⟨⟨result.1, valid.2⟩, result.2.1.inLeft, by
      simp only [Partitioned.credit]; have bound := result.2.2; omega⟩
  | right step ih =>
    have result := ih valid.2
    exact ⟨⟨valid.1, result.1⟩, result.2.1.inRight, by
      simp only [Partitioned.credit]; have bound := result.2.2; omega⟩

/-- Arbitrarily interleaved refinements spend one initial budget, rather than
receiving a fresh linear allowance on every row. -/
theorem Refinement.spec {s t : Partitioned} {cost : Nat} (steps : Refinement s t cost) (valid : s.Valid) :
    t.Valid ∧ Rotations s.tree t.tree cost ∧ cost + t.credit ≤ s.credit := by
  induction steps with
  | refl => exact ⟨valid, .refl, by omega⟩
  | step first rest ih =>
    have firstResult := first.spec valid
    have restResult := ih firstResult.1
    exact ⟨restResult.1, firstResult.2.1.append restResult.2.1, by
      have h1 := firstResult.2.2; have h2 := restResult.2.2; omega⟩

theorem intervalCredit_linear (input : Option State) :
    intervalCredit input ≤ 6014 * (intervalTree input).size := by
  have nodes := intervalNodes_le_size input
  simp only [intervalCredit]
  omega

theorem Refinement.linear {input : Option State} {output : Partitioned} {cost : Nat}
    (steps : Refinement (.leaf input) output cost) (valid : IntervalValid input) :
    cost + output.credit ≤ 6014 * (intervalTree input).size :=
  (steps.spec valid).2.2.trans (intervalCredit_linear input)

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
