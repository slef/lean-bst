module

public import RotationBST.Algorithms.Combination.Refinement.Visits.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Worker.Pair

/-- Tag only the active input worker. The selected source sides are fixed
when the pair is built, and a step never runs the other input. -/
def worker {α β : Type} (left : Controller.Worker α) (right : Controller.Worker β)
    (leftSide rightSide : Bool) : Controller.Worker (Sum α β) where
  restart := fun side => if side then .inr (right.restart rightSide) else .inl (left.restart leftSide)
  step := fun side state x => match side, state with
    | false, .inl s => let next := left.step leftSide s x; (.inl next.1, next.2)
    | true, .inr s => let next := right.step rightSide s x; (.inr next.1, next.2)
    | _, s => (s, false)

/-- Each paired side retains the selected input's original charge function. -/
def charges (left right : Analysis.Charges) (leftSide rightSide : Bool) : Analysis.Charges :=
  fun side => if side then right rightSide else left leftSide

/-- The tagged worker has exactly its selected source cursor and invariant.
Mismatched tags are not ready and cannot be reached from a paired restart. -/
def model {α β : Type} {left : Controller.Worker α} {right : Controller.Worker β} {saved : Tree}
    (leftModel : Refinement.WorkerModel left saved) (rightModel : Refinement.WorkerModel right saved)
    (leftSide rightSide : Bool) : Refinement.WorkerModel (worker left right leftSide rightSide) saved where
  cursor := fun _ state => match state with
    | .inl s => leftModel.cursor leftSide s
    | .inr s => rightModel.cursor rightSide s
  Ready := fun side state => match side, state with
    | false, .inl s => leftModel.Ready leftSide s
    | true, .inr s => rightModel.Ready rightSide s
    | _, _ => False
  instruction := fun _ state x => match state with
    | .inl s => leftModel.instruction leftSide s x
    | .inr s => rightModel.instruction rightSide s x
  restart_ready := by intro side; cases side <;> exact (by first | exact leftModel.restart_ready _ | exact rightModel.restart_ready _)
  restart_cursor := by intro side; cases side <;> exact (by first | exact leftModel.restart_cursor _ | exact rightModel.restart_cursor _)
  size := by
    intro side state ready
    cases side <;> cases state <;> first | contradiction | exact leftModel.size _ _ ready | exact rightModel.size _ _ ready
  step_ready := by
    intro side state x ready valid
    cases side <;> cases state <;> first | contradiction | exact leftModel.step_ready _ _ _ ready valid | exact rightModel.step_ready _ _ _ ready valid
  step_cursor := by
    intro side state x ready valid
    cases side <;> cases state <;> first | contradiction | exact leftModel.step_cursor _ _ _ ready valid | exact rightModel.step_cursor _ _ _ ready valid

end RotationBST.Combo.Worker.Pair
