module

public import RotationBST.Algorithms.Combination.Worker.Pair.Abstract
public import RotationBST.Algorithms.Combination.Online.Replay.Abstract
public import RotationBST.Algorithms.Combination.Family.Abstract
public import RotationBST.Algorithms.Combination.Family.Physical.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.WorkerPair
open Combo

private def saved : Tree := .node .nil .nil
private def left : Controller.Worker Nat :=
  ⟨fun _ => 0, fun side state _ => (state + if side then 2 else 1, true)⟩
private def right : Controller.Worker Bool := ⟨id, fun _ state _ => (false, !state)⟩
private def paired := Worker.Pair.worker left right true true

-- The pair's false side selects the left worker's true side, retaining its
-- actual successor state and the unconsumed budget.
example : Controller.attempt paired false 0 3 (.inl 5) = ⟨.inl 7, 2, true⟩ := by cbv

-- The right input uses a different state type and can stop between its ticks.
example : Controller.attempt paired true 0 1 (.inr true) = ⟨.inr false, 0, false⟩ := by cbv
example : Controller.attempt paired true 0 1 (.inr false) = ⟨.inr false, 0, true⟩ := by cbv
example : Controller.attempt paired true 0 5 (.inr true) = ⟨.inr false, 3, true⟩ := by cbv

-- A mismatched tag is not treated as a completed request.
example : Controller.attempt paired false 0 5 (.inr true) = ⟨.inr true, 0, false⟩ := by cbv

example : Worker.Access paired true (.inr true) 0 (.inr false) 2 :=
  (Worker.Pair.Results.access_right left right true true).mpr
    ⟨false, rfl, .more rfl (.done (fuel := 0) rfl)⟩

example (run : Worker.Requests paired false (.inl 0) [0, 0, 0] (.inl 6) 3) :
    ∃ final, Sum.inl 6 = (Sum.inl final : Sum Nat Bool) ∧ Worker.Requests left true 0 [0, 0, 0] final 3 :=
  (Worker.Pair.Results.requests_left left right true true).mp run

private def rootModel {σ : Type} (worker : Controller.Worker σ) : Refinement.WorkerModel worker saved where
  cursor := fun _ _ => ⟨saved, []⟩
  Ready := fun _ _ => True
  instruction := fun _ _ _ => none
  restart_ready := fun _ => trivial
  restart_cursor := fun _ => rfl
  size := fun _ _ _ => rfl
  step_ready := fun _ _ _ _ _ => trivial
  step_cursor := fun _ _ _ _ _ => rfl

private theorem rootCorrect {σ : Type} (worker : Controller.Worker σ) : Refinement.Visits.Correct (rootModel worker) := by
  intro side state x final cost boundary valid ran
  have key : x = 0 := by change x < 1 at valid; omega
  subst x
  cases cost with
  | zero => rfl
  | succ cost => exact Or.inl rfl

private def leftCharges : Analysis.Charges := fun _ _ _ => 1
private def rightCharges : Analysis.Charges := fun _ _ _ => 2

private theorem leftRequests (side : Bool) (state : Nat) (xs : List Nat) :
    ∃ final, Worker.Requests left side state xs final xs.length := by
  induction xs generalizing state with
  | nil => exact ⟨state, .nil⟩
  | cons x xs ih =>
    obtain ⟨final, rest⟩ := ih (left.step side state x).1
    exact ⟨final, by simpa only [List.length_cons, Nat.add_comm 1] using
      Worker.Requests.cons (Controller.AttemptRun.done (fuel := 0) rfl) rest⟩

private theorem rightAccess (side state : Bool) (x : Nat) :
    ∃ final cost, Worker.Access right side state x final cost ∧ cost ≤ 2 := by
  cases state
  · exact ⟨false, 1, .done (fuel := 0) rfl, by decide⟩
  · exact ⟨false, 2, .more rfl (.done (fuel := 0) rfl), by decide⟩

private theorem rightRequests (side state : Bool) (xs : List Nat) :
    ∃ final cost, Worker.Requests right side state xs final cost ∧ cost ≤ 2 * xs.length := by
  induction xs generalizing state with
  | nil => exact ⟨state, 0, .nil, by simp⟩
  | cons x xs ih =>
    obtain ⟨middle, firstCost, first, firstBound⟩ := rightAccess side state x
    obtain ⟨final, restCost, rest, restBound⟩ := ih middle
    exact ⟨final, firstCost + restCost, .cons first rest, by simp only [List.length_cons]; omega⟩

private theorem leftWell : Analysis.WellBehaved left saved.size 2 1 1 leftCharges := by
  constructor
  · intro side xs i; norm_num [leftCharges]
  · intro side earlier state spent ran validEarlier x valid
    exact ⟨_, 1, .done (fuel := 0) rfl, by decide⟩
  · intro side xs valid
    obtain ⟨final, ran⟩ := leftRequests side 0 xs
    exact ⟨final, xs.length, ran, by simp [Analysis.total, Analysis.mass, leftCharges]⟩
  · intro side xs valid lo hi ordered inside
    have length : (Analysis.segment xs lo hi).length = hi - lo := by
      simp only [Analysis.segment, List.length_take, List.length_drop]; omega
    simp [Analysis.total, Analysis.mass, leftCharges, length]

private theorem rightWell : Analysis.WellBehaved right saved.size 2 1 1 rightCharges := by
  constructor
  · intro side xs i; norm_num [rightCharges]
  · intro side earlier state spent ran validEarlier x valid
    exact rightAccess side state x
  · intro side xs valid
    obtain ⟨final, cost, ran, bound⟩ := rightRequests side side xs
    refine ⟨final, cost, ran, ?_⟩
    have realBound : (cost : ℝ) ≤ 2 * xs.length := by exact_mod_cast bound
    simpa [Analysis.total, Analysis.mass, rightCharges, mul_comm] using
      (show (cost : ℝ) ≤ 2 * (xs.length : ℝ) + 2 by linarith)
  · intro side xs valid lo hi ordered inside
    have length : (Analysis.segment xs lo hi).length = hi - lo := by
      simp only [Analysis.segment, List.length_take, List.length_drop]; omega
    simp [Analysis.total, Analysis.mass, rightCharges, length]

private theorem pairedCorrect : Refinement.Visits.Correct (Worker.Pair.model (rootModel left) (rootModel right) true true) :=
  Worker.Pair.Results.correct (rootModel left) (rootModel right) true true (rootCorrect left) (rootCorrect right)

private theorem pairedWell : Analysis.WellBehaved paired saved.size 2 1 1
    (Worker.Pair.charges leftCharges rightCharges true true) :=
  Worker.Pair.Results.well_behaved leftWell rightWell true true

-- Pairing has no additional cost factor: the controller executes four left
-- requests, then restarts the right worker to complete the fifth.
example : Controller.run paired 4 114 (Controller.initial paired 4) [0, 0, 0, 0, 0] =
    some (⟨true, .inr false, 2⟩, 120) := by cbv

-- The heterogeneous pair feeds the online transformation and inherits bounds
-- for the distinct original charge functions, with a common initial tree.
example : ∃ p : Online.Prepared (Worker.Pair.model (rootModel left) (rootModel right) true true)
    4 114 (fun _ => ⟨0, 1⟩) (fun _ => 0),
    ∃ implementation : Online.Replay.Implementation p,
      Analysis.WellBehaved (Worker.Replay.worker implementation.planner) saved.size
        14219266 1 2 (Online.Replay.scaledCharges 1978624 (Worker.Pair.charges leftCharges rightCharges true true)) := by
  obtain ⟨p, implementation, _, well⟩ := Online.Replay.Results.combine
    (Worker.Pair.model (rootModel left) (rootModel right) true true) pairedCorrect pairedWell
    (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)
  exact ⟨p, implementation, well⟩

-- Three inputs require padding, and retain heterogeneous state types and
-- different charge functions. The third comparator repeats the first.
private def familyInputs (i : Fin 3) : Family.Algorithm saved :=
  if i = 1 then ⟨Bool, right, rootModel right, rootCorrect right⟩
  else ⟨Nat, left, rootModel left, rootCorrect left⟩

private def familyCharges (i : Fin 3) : Family.Charge :=
  if i = 1 then fun _ _ => 2 else fun _ _ => 1

private theorem familyWell (i : Fin 3) :
    Analysis.WellBehaved (familyInputs i).worker saved.size 2 1 1 (fun _ => familyCharges i) := by
  fin_cases i <;> first | exact leftWell | exact rightWell

-- The policy is chosen before either the prefix or comparator is supplied.
-- Padding from three inputs to four leaves takes exactly two levels.
example : ∃ output : Family.Algorithm saved,
    Family.Guarantees output (Family.overheadScale 1 1 2 * 2) 1 3 (Family.chargeScale 1 1 2) familyCharges ∧
    ∀ side xs, (∀ x ∈ xs, x < saved.size) →
      ∃ final cost, Worker.Requests output.worker side (output.worker.restart side) xs final cost ∧
        (cost : ℝ) ≤ (Family.chargeScale 1 1 2 : ℝ) * Family.minimum familyCharges xs +
          (Family.overheadScale 1 1 2 * 2 : Nat) := by
  simpa only [Fintype.card_fin, show Nat.clog 2 3 = 2 by decide, show (1 : Nat) + 2 = 3 by rfl] using Family.Results.minimum_policy 2 1 1 familyInputs familyCharges familyWell
    (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)

-- All three comparisons refer to the same run and state. The empty prefix
-- incurs no initialization; the nonempty prefix retains the different bounds.
example : ∃ output : Family.Algorithm saved,
    Worker.Requests output.worker false (output.worker.restart false) [] (output.worker.restart false) 0 ∧
    ∃ final cost, Worker.Requests output.worker false (output.worker.restart false) [0, 0, 0] final cost ∧
      (cost : ℝ) ≤ (Family.chargeScale 1 1 2 : ℝ) * 3 + (Family.overheadScale 1 1 2 * 2 : Nat) ∧
      (cost : ℝ) ≤ (Family.chargeScale 1 1 2 : ℝ) * 6 + (Family.overheadScale 1 1 2 * 2 : Nat) := by
  obtain ⟨output, guaranteed⟩ := Family.Results.finite 2 2 1 1 (by decide)
    familyInputs familyCharges familyWell (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)
  obtain ⟨final, cost, ran, bounds⟩ := Family.Results.requests output guaranteed false [0, 0, 0]
    (by simp [saved, Tree.size])
  refine ⟨output, .nil, final, cost, ran, ?_, ?_⟩
  · simpa [Family.total, Analysis.total, Analysis.mass, familyCharges] using bounds (0 : Fin 3)
  · have bound := bounds (1 : Fin 3)
    norm_num [Family.total, Analysis.total, Analysis.mass, familyCharges] at bound ⊢
    exact bound

-- A singleton family has depth zero, so there is no combination overhead.
example : ∃ output : Family.Algorithm saved,
    Family.Guarantees output 2 1 1 1 (fun (_ : Unit) _ _ => (1 : ℝ)) := by
  simpa [Family.overheadScale, Family.chargeScale] using
    Family.Results.exists_combination 2 1 1
      (fun (_ : Unit) => (⟨Nat, left, rootModel left, rootCorrect left⟩ : Family.Algorithm saved))
      (fun (_ : Unit) _ _ => (1 : ℝ)) (fun _ => leftWell)
      (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)

-- The three-input construction also has one fixed physical policy. Its
-- bounds concern real request-serving executions and their actual windows.
example : ∃ output : Family.Algorithm saved,
    Family.Guarantees output (Family.overheadScale 1 1 2 * 2) 1 3 (Family.chargeScale 1 1 2) familyCharges ∧
    ∃ p : Online.Prepared output.model (Analysis.budget (Family.overheadScale 1 1 2 * 2) 3)
        (57 * (Family.overheadScale 1 1 2 * 2)) (fun _ => ⟨0, 1⟩) (fun _ => 0),
      Family.Physical.Bounded p (Family.Physical.chargeFactor 1 3 (Family.chargeScale 1 1 2))
        (Family.Physical.overheadFactor 1 3 * (Family.overheadScale 1 1 2 * 2)) familyCharges := by
  have policy := Family.Physical.Results.finite_policy 2 1 1 familyInputs familyCharges familyWell
    (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)
  dsimp only at policy
  rw [Fintype.card_fin, show Nat.clog 2 3 = 2 by decide] at policy
  exact policy

-- A window after the first request uses the state left by that request.
-- It is part of the original execution, with exactly additive costs.
example : ∃ output : Family.Algorithm saved,
    ∃ p : Online.Prepared output.model (Analysis.budget (Family.overheadScale 1 1 2 * 2) 3)
        (57 * (Family.overheadScale 1 1 2 * 2)) (fun _ => ⟨0, 1⟩) (fun _ => 0),
      let first := Online.execute p none [0]
      let middle := Online.execute p first.1 [0, 0]
      Online.execute p none [0, 0, 0] = (middle.1, first.2 + middle.2) ∧
        Pointer.Execution (p.current first.1) [0, 0] (p.current middle.1) middle.2 ∧
        (middle.2 : ℝ) ≤ (Family.Physical.chargeFactor 1 3 (Family.chargeScale 1 1 2) : ℝ) * 2 +
          (Family.Physical.overheadFactor 1 3 * (Family.overheadScale 1 1 2 * 2) : Nat) ∧
        Online.execute p first.1 [] = (first.1, 0) := by
  obtain ⟨output, guaranteed, p, _⟩ := Family.Physical.Results.combine 2 2 1 1 (by decide)
    familyInputs familyCharges familyWell (by decide) (by decide) (fun _ => ⟨0, 1⟩) (fun _ => 0)
  have levelSize : saved.size ≤ Family.overheadScale 1 1 2 * 2 := by
    exact (show saved.size ≤ 2 by decide).trans
      (Nat.le_mul_of_pos_left _ (Family.Results.overheadScale_pos 1 1 2))
  obtain ⟨split, physical, bounds⟩ := Family.Physical.Results.executed_window output guaranteed p levelSize
    [0, 0, 0] (by simp [saved, Tree.size]) 1 3 (by decide) (by decide)
  refine ⟨output, p, ?_, ?_, ?_, rfl⟩
  · exact split
  · simpa only [Analysis.segment, List.take, List.drop] using physical
  · simpa [Family.Physical.mass, Analysis.mass, Analysis.segment, familyCharges] using bounds (0 : Fin 3)

-- Original indices are essential: slicing and restarting the charge function
-- would incorrectly replace charges 2 + 3 by charges 1 + 2.
example : Family.Physical.mass (fun _ i => (i + 1 : Nat)) [0, 0, 0] 1 3 = 5 := by
  norm_num [Family.Physical.mass, Analysis.mass, Finset.sum_Ico_succ_top]

example : Family.total (fun _ i => (i + 1 : Nat)) (Analysis.segment [0, 0, 0] 1 3) = 3 := by
  norm_num [Family.total, Analysis.total, Analysis.mass, Analysis.segment, Finset.sum_Ico_succ_top]

-- The best comparator can differ between windows of the same sequence.
private def crossingCharges (side : Bool) : Family.Charge := fun _ i =>
  if side then (if i = 0 then 10 else 1) else (if i = 0 then 1 else 10)

example : Family.Physical.minimumMass crossingCharges [0, 0] 0 1 = 1 := by
  norm_num [Family.Physical.minimumMass, Family.Physical.mass, Analysis.mass,
    crossingCharges, show (Finset.univ : Finset Bool) = {false, true} by decide, Finset.sum_Ico_succ_top]

example : Family.Physical.minimumMass crossingCharges [0, 0] 1 2 = 1 := by
  norm_num [Family.Physical.minimumMass, Family.Physical.mass, Analysis.mass,
    crossingCharges, show (Finset.univ : Finset Bool) = {false, true} by decide, Finset.sum_Ico_succ_top]

end RotationBST.Tests.WorkerPair
