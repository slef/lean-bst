module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Transition.Abstract
public import RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Extraction
public import RotationBST.Arboral.Online.LastTouch.Supernode.Accounting.Rebuild
public import RotationBST.Arboral.Online.LastTouch.Supernode.Extraction.Completion

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Each legal row has a concrete next state and an amortized rotation bound.
Old credit pays for extraction; only the current row allocates new credit. -/
theorem nextState_spec {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    {state : Nested} (represented : Represents P 0 state) (size : state.tree.size = n) :
    Represents (P ∪ row time keys) 0 (nextState state keys) ∧
      ∃ cost, Rotations state.tree (nextState state keys).tree cost ∧
        cost + (nextState state keys).credit ≤ state.credit + 6016 * keys.card := by
  have extracted := extractRow_spec history legal represented
  have fullRow : Region.keys (extractRow keys 0 state).1.region 0 = keys := by
    rw [extracted.2.2, size, Nat.zero_add]
    apply Finset.inter_eq_left.mpr
    intro key member
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, Finset.mem_range.mp (legal.2.1 member)⟩
  have rebuilt := Assembly.rebuild_spec history extracted.1
  have paid := Assembly.rebuild_budget history extracted.1
  rw [fullRow] at rebuilt paid
  obtain ⟨rebuildCost, rotations, budget⟩ := paid
  have extractionBudget := extract_credit (state.tree.size + 1) keys represented
  change (extractRow keys 0 state).2 + (extractRow keys 0 state).1.credit ≤ state.credit at extractionBudget
  refine ⟨rebuilt.1, (extractRow keys 0 state).2 + rebuildCost, extracted.2.1.append rotations, ?_⟩
  change _ + _ + (extractRow keys 0 state).1.rebuild.credit ≤ _
  omega

end RotationBST.Arboral.Online.Supernode
