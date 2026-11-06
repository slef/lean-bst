module

public import RotationBST.Structures.TreeBuffer.Shared.CellRefinement.Steps

@[expose] public section
namespace RotationBST.TreeBuffer.Shared.CellRefinement

/-- Lift a whole cell-access phase, preserving its exact event stream and every
inactive finger. Only the selected buffer finger navigates during this phase. -/
theorem trace {α : Type} {fingers : Nat} {s t : Cells.State α} {events : List (Cells.Event α)}
    {work rotations : Nat} (run : Cells.Trace s t events work rotations) (zero : rotations = 0)
    (valid : s.scan.Valid) (actual : Shared.State α fingers) (i : Fin fingers)
    (represented : Represents actual s i) :
    ∃ final cost, Shared.Trace actual final events cost ∧ Represents final t i ∧
      (∀ j, j ≠ i → final.position j = actual.position j) ∧ cost ≤ 4 * work := by
  induction run generalizing actual with
  | refl => exact ⟨actual, 0, .refl, represented, fun _ _ => rfl, Nat.le_refl _⟩
  | @step s t u event events w r v q first tail ih =>
    obtain ⟨middle, firstCost, action, middleRep, firstBound⟩ :=
      step first (by omega) valid actual i represented
    obtain ⟨final, restCost, rest, finalRep, inactive, bound⟩ :=
      ih (by omega) (first.scan.valid valid) middle middleRep
    refine ⟨final, firstCost + restCost, action.trace.append rest, finalRep, ?_, ?_⟩
    · intro j different
      exact (inactive j different).trans (action.inactive different)
    · omega

end RotationBST.TreeBuffer.Shared.CellRefinement
