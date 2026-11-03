module

public import RotationBST.Algorithms.Simulation.Supernode.Transition.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Assembly.Access

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- Serve the request at the root, then restore the canonical next state.
Both parts are charged: exposing and restoring the root adds at most two
rotations per current-row point to the amortized transition bound. -/
theorem nextState_access {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    {state : Nested} (represented : Represents P 0 state) (size : state.tree.size = n) :
    Represents (P ∪ row time keys) 0 (nextState state keys) ∧
      ∃ served accessCost restoreCost,
        Access state.tree served request accessCost ∧
        Rotations served (nextState state keys).tree restoreCost ∧
        accessCost + restoreCost + (nextState state keys).credit ≤ state.credit + 6018 * keys.card := by
  have extracted := extractRow_spec history legal represented
  have fullRow : Region.keys (extractRow keys 0 state).1.region 0 = keys := by
    rw [extracted.2.2, size, Nat.zero_add]
    apply Finset.inter_eq_left.mpr
    intro key member
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, Finset.mem_range.mp (legal.2.1 member)⟩
  have visited : request ∈ Region.keys (extractRow keys 0 state).1.region 0 := by
    rw [fullRow]; exact legal.1
  obtain ⟨served, visitCost, access, visitBound⟩ := Assembly.access visited
  obtain ⟨rebuildCost, rebuildSteps, rebuildBound⟩ := Assembly.rebuild_budget history extracted.1
  rw [fullRow] at visitBound rebuildBound
  have extractionBound := extract_credit (state.tree.size + 1) keys represented
  change (extractRow keys 0 state).2 + (extractRow keys 0 state).1.credit ≤ state.credit at extractionBound
  refine ⟨(nextState_spec history legal represented size).1, served,
    (extractRow keys 0 state).2 + visitCost, visitCost + rebuildCost,
    ⟨extracted.2.1.append access.1, access.2⟩, access.1.symm.append rebuildSteps, ?_⟩
  change _ + _ + (extractRow keys 0 state).1.rebuild.credit ≤ _
  omega

end RotationBST.Arboral.Online.Supernode
