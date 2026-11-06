module

public import RotationBST.Algorithms.Combination.Worker.Pair.Visits

@[expose] public section
namespace RotationBST.Combo.Worker.Pair

/-- Pairing changes neither input costs nor their charge functions. Common
well-behaved constants therefore transfer without an extra factor or overhead. -/
theorem well_behaved {α β : Type} {left : Controller.Worker α} {right : Controller.Worker β}
    {n overhead C₀ C₁ : Nat} {leftCharges rightCharges : Analysis.Charges}
    (leftWell : Analysis.WellBehaved left n overhead C₀ C₁ leftCharges)
    (rightWell : Analysis.WellBehaved right n overhead C₀ C₁ rightCharges)
    (leftSide rightSide : Bool) :
    Analysis.WellBehaved (worker left right leftSide rightSide) n overhead C₀ C₁
      (charges leftCharges rightCharges leftSide rightSide) := by
  constructor
  · intro side xs i
    cases side
    · exact leftWell.nonneg leftSide xs i
    · exact rightWell.nonneg rightSide xs i
  · intro side earlier state spent priorRun validEarlier x valid
    cases side with
    | false =>
      obtain ⟨original, rfl, sourcePrefix⟩ := (requests_left left right leftSide rightSide).mp priorRun
      obtain ⟨next, cost, sourceRun, bound⟩ := leftWell.single leftSide earlier original spent sourcePrefix validEarlier x valid
      exact ⟨.inl next, cost, (access_left left right leftSide rightSide).mpr ⟨next, rfl, sourceRun⟩, bound⟩
    | true =>
      obtain ⟨original, rfl, sourcePrefix⟩ := (requests_right left right leftSide rightSide).mp priorRun
      obtain ⟨next, cost, sourceRun, bound⟩ := rightWell.single rightSide earlier original spent sourcePrefix validEarlier x valid
      exact ⟨.inr next, cost, (access_right left right leftSide rightSide).mpr ⟨next, rfl, sourceRun⟩, bound⟩
  · intro side xs valid
    cases side with
    | false =>
      obtain ⟨next, cost, ran, bound⟩ := leftWell.upper leftSide xs valid
      exact ⟨.inl next, cost, (requests_left left right leftSide rightSide).mpr ⟨next, rfl, ran⟩, bound⟩
    | true =>
      obtain ⟨next, cost, ran, bound⟩ := rightWell.upper rightSide xs valid
      exact ⟨.inr next, cost, (requests_right left right leftSide rightSide).mpr ⟨next, rfl, ran⟩, bound⟩
  · intro side xs valid lo hi ordered inside
    cases side
    · exact leftWell.stable leftSide xs valid lo hi ordered inside
    · exact rightWell.stable rightSide xs valid lo hi ordered inside

end RotationBST.Combo.Worker.Pair
