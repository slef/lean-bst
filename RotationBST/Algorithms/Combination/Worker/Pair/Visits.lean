module

public import RotationBST.Algorithms.Combination.Worker.Pair.Execution

@[expose] public section
namespace RotationBST.Combo.Worker.Pair

variable {α β : Type} {left : Controller.Worker α} {right : Controller.Worker β} {saved : Tree}
  (leftModel : Refinement.WorkerModel left saved) (rightModel : Refinement.WorkerModel right saved)
  (leftSide rightSide : Bool)

theorem seen_left (x count : Nat) (state : α) :
    Refinement.Visits.Seen (model leftModel rightModel leftSide rightSide) false x count (.inl state) ↔
      Refinement.Visits.Seen leftModel leftSide x count state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change ((leftModel.cursor leftSide state).key? = some x ∨
      Refinement.Visits.Seen (model leftModel rightModel leftSide rightSide) false x count
        (.inl (left.step leftSide state x).1)) ↔ _
    rw [ih]
    rfl

theorem seen_right (x count : Nat) (state : β) :
    Refinement.Visits.Seen (model leftModel rightModel leftSide rightSide) true x count (.inr state) ↔
      Refinement.Visits.Seen rightModel rightSide x count state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    change ((rightModel.cursor rightSide state).key? = some x ∨
      Refinement.Visits.Seen (model leftModel rightModel leftSide rightSide) true x count
        (.inr (right.step rightSide state x).1)) ↔ _
    rw [ih]
    rfl

theorem correct (leftCorrect : Refinement.Visits.Correct leftModel) (rightCorrect : Refinement.Visits.Correct rightModel) :
    Refinement.Visits.Correct (model leftModel rightModel leftSide rightSide) := by
  intro side state x final cost boundary valid ran
  obtain ⟨earlier, spent, priorRun, validEarlier⟩ := boundary
  cases side with
  | false =>
    obtain ⟨original, rfl, sourcePrefix⟩ := (requests_left left right leftSide rightSide).mp priorRun
    obtain ⟨next, _, sourceRun⟩ := (access_left left right leftSide rightSide).mp ran
    exact (seen_left leftModel rightModel leftSide rightSide x cost original).mpr
      (leftCorrect leftSide original x next cost ⟨earlier, spent, sourcePrefix, validEarlier⟩ valid sourceRun)
  | true =>
    obtain ⟨original, rfl, sourcePrefix⟩ := (requests_right left right leftSide rightSide).mp priorRun
    obtain ⟨next, _, sourceRun⟩ := (access_right left right leftSide rightSide).mp ran
    exact (seen_right leftModel rightModel leftSide rightSide x cost original).mpr
      (rightCorrect rightSide original x next cost ⟨earlier, spent, sourcePrefix, validEarlier⟩ valid sourceRun)

end RotationBST.Combo.Worker.Pair
