module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Worker.Pair.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Worker.Pair.Results

theorem attempt_left {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) (x fuel : Nat) (state : α) :
    Controller.attempt (worker left right leftSide rightSide) false x fuel (.inl state) =
      let result := Controller.attempt left leftSide x fuel state
      ⟨.inl result.state, result.left, result.done⟩ :=
  RotationBST.Combo.Worker.Pair.attempt_left left right leftSide rightSide x fuel state

theorem attempt_right {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) (x fuel : Nat) (state : β) :
    Controller.attempt (worker left right leftSide rightSide) true x fuel (.inr state) =
      let result := Controller.attempt right rightSide x fuel state
      ⟨.inr result.state, result.left, result.done⟩ :=
  RotationBST.Combo.Worker.Pair.attempt_right left right leftSide rightSide x fuel state

theorem access_left {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) {state : α} {final : Sum α β} {x cost : Nat} :
    Worker.Access (worker left right leftSide rightSide) false (.inl state) x final cost ↔
      ∃ next, final = .inl next ∧ Worker.Access left leftSide state x next cost :=
  RotationBST.Combo.Worker.Pair.access_left left right leftSide rightSide

theorem access_right {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) {state : β} {final : Sum α β} {x cost : Nat} :
    Worker.Access (worker left right leftSide rightSide) true (.inr state) x final cost ↔
      ∃ next, final = .inr next ∧ Worker.Access right rightSide state x next cost :=
  RotationBST.Combo.Worker.Pair.access_right left right leftSide rightSide

theorem requests_left {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) {state : α} {final : Sum α β} {xs : List Nat} {cost : Nat} :
    Worker.Requests (worker left right leftSide rightSide) false (.inl state) xs final cost ↔
      ∃ next, final = .inl next ∧ Worker.Requests left leftSide state xs next cost :=
  RotationBST.Combo.Worker.Pair.requests_left left right leftSide rightSide

theorem requests_right {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β) (leftSide rightSide : Bool) {state : β} {final : Sum α β} {xs : List Nat} {cost : Nat} :
    Worker.Requests (worker left right leftSide rightSide) true (.inr state) xs final cost ↔
      ∃ next, final = .inr next ∧ Worker.Requests right rightSide state xs next cost :=
  RotationBST.Combo.Worker.Pair.requests_right left right leftSide rightSide

theorem correct {α β : Type} {left : Controller.Worker α} {right : Controller.Worker β} {saved : Tree}
    (leftModel : Refinement.WorkerModel left saved) (rightModel : Refinement.WorkerModel right saved)
    (leftSide rightSide : Bool) (leftCorrect : Refinement.Visits.Correct leftModel) (rightCorrect : Refinement.Visits.Correct rightModel) :
    Refinement.Visits.Correct (model leftModel rightModel leftSide rightSide) :=
  RotationBST.Combo.Worker.Pair.correct leftModel rightModel leftSide rightSide leftCorrect rightCorrect

theorem well_behaved {α β : Type} {left : Controller.Worker α} {right : Controller.Worker β}
    {n overhead C₀ C₁ : Nat} {leftCharges rightCharges : Analysis.Charges}
    (leftWell : Analysis.WellBehaved left n overhead C₀ C₁ leftCharges)
    (rightWell : Analysis.WellBehaved right n overhead C₀ C₁ rightCharges)
    (leftSide rightSide : Bool) :
    Analysis.WellBehaved (worker left right leftSide rightSide) n overhead C₀ C₁
      (charges leftCharges rightCharges leftSide rightSide) :=
  RotationBST.Combo.Worker.Pair.well_behaved leftWell rightWell leftSide rightSide

end RotationBST.Combo.Worker.Pair.Results

/-- info: abstract audit passed for `RotationBST.Combo.Worker.Pair.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Worker.Pair.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Definitions.Abstract,
  RotationBST.Models.Labelled.Cursor.Map.Definitions.Abstract,
  RotationBST.Models.Labelled.Metadata.Definitions.Abstract,
  RotationBST.Models.Labelled.Intervals.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Nodes.Definitions.Abstract,
  RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Controller.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Rounds.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Worker.Pair.Definitions.Abstract]
