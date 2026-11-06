module

public import RotationBST.Algorithms.Combination.Controller.Sequences

@[expose] public section
namespace RotationBST.Combo.Controller

/-- Every reached request boundary retains at most one round's budget. -/
theorem Execution.left_le {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s xs t cost switches) (limit : s.left ≤ budget) : t.left ≤ budget := by
  induction execution with
  | nil => exact limit
  | cons _ _ ih => exact ih (serve_left _ _ _ _ _ limit)

/-- Splitting an executed input preserves the exact intermediate state, work,
and switch counts; neither part restarts the controller. -/
theorem Execution.split {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs ys : List Nat} {cost switches : Nat}
    (execution : Execution worker budget restore s (xs ++ ys) t cost switches) :
    ∃ middle beforeCost afterCost beforeSwitches afterSwitches,
      Execution worker budget restore s xs middle beforeCost beforeSwitches ∧
      Execution worker budget restore middle ys t afterCost afterSwitches ∧
      cost = beforeCost + afterCost ∧ switches = beforeSwitches + afterSwitches := by
  induction xs generalizing s cost switches with
  | nil => exact ⟨s, 0, cost, 0, switches, .nil, execution, by simp, by simp⟩
  | cons x xs ih =>
    cases execution with
    | cons done tail =>
      obtain ⟨middle, beforeCost, afterCost, beforeSwitches, afterSwitches, first, second, work, changed⟩ := ih tail
      exact ⟨middle, _, afterCost, _, afterSwitches, .cons done first, second, by omega, by omega⟩

/-- The cost of a contiguous window is exactly the middle summand of the
original execution, including any switch charged to a request in that window. -/
theorem Execution.window {σ : Type} {worker : Worker σ} {budget restore : Nat}
    {s t : State σ} {xs : List Nat} {cost switches lo hi : Nat}
    (execution : Execution worker budget restore s xs t cost switches) (ordered : lo ≤ hi) :
    ∃ beforeState afterState beforeCost windowCost afterCost beforeSwitches windowSwitches afterSwitches,
      Execution worker budget restore s (xs.take lo) beforeState beforeCost beforeSwitches ∧
      Execution worker budget restore beforeState ((xs.drop lo).take (hi - lo)) afterState windowCost windowSwitches ∧
      Execution worker budget restore afterState (xs.drop hi) t afterCost afterSwitches ∧
      cost = beforeCost + windowCost + afterCost ∧ switches = beforeSwitches + windowSwitches + afterSwitches := by
  have firstSplit : Execution worker budget restore s (xs.take lo ++ xs.drop lo) t cost switches := by
    simpa only [List.take_append_drop] using execution
  obtain ⟨beforeState, beforeCost, restCost, beforeSwitches, restSwitches, first, rest, work, changed⟩ := firstSplit.split
  have secondSplit : Execution worker budget restore beforeState
      ((xs.drop lo).take (hi - lo) ++ (xs.drop lo).drop (hi - lo)) t restCost restSwitches := by
    simpa only [List.take_append_drop] using rest
  obtain ⟨afterState, windowCost, afterCost, windowSwitches, afterSwitches, middle, last, restWork, restChanged⟩ := secondSplit.split
  refine ⟨beforeState, afterState, beforeCost, windowCost, afterCost, beforeSwitches, windowSwitches, afterSwitches,
    first, middle, ?_, by omega, by omega⟩
  simpa only [List.drop_drop, Nat.add_sub_of_le ordered] using last

end RotationBST.Combo.Controller
