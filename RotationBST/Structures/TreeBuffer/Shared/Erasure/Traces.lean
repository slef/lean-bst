module

public import RotationBST.Structures.TreeBuffer.Shared.Erasure.Steps
public import RotationBST.Structures.TreeBuffer.Shared.Requests.Visits

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Erasing fields projects the entire shared trace, retaining all persistent
positions and using no more pointer instructions than the charged shared work. -/
theorem Trace.erase {α : Type} {fingers : Nat} {s t : State α fingers} {events : List (Cells.Event α)} {cost : Nat}
    (trace : Trace s t events cost) (data : Nat → α) (valid : s.Valid data) :
    ∃ touches, Multifinger.Trace s.erase touches t.erase ∧ touches.length ≤ cost := by
  induction trace generalizing data with
  | refl => exact ⟨[], .refl, Nat.le_refl _⟩
  | step first _ ih =>
    obtain ⟨before, firstRun, firstBound⟩ := first.erase data valid
    obtain ⟨after, lastRun, lastBound⟩ := ih _ (first.valid data valid)
    exact ⟨before ++ after, firstRun.append lastRun, by simp only [List.length_append]; omega⟩

/-- A visit at a shared finger is a visit at the very same multifinger node.
The additional request unit is retained in the conventional cost definition. -/
theorem Requests.Visit.erase {α : Type} {fingers : Nat} {s t : State α fingers} {events : List (Cells.Event α)} {x cost : Nat}
    (visit : Requests.Visit s t x events cost) (data : Nat → α) (valid : s.Valid data) :
    ∃ work, Multifinger.Serves s.erase t.erase x work ∧ work ≤ 1 + cost := by
  obtain ⟨middle, before, after, first, last, i, left, key, right, rfl, rfl⟩ := visit
  obtain ⟨beforeTouches, firstRun, firstBound⟩ := left.erase data valid
  obtain ⟨afterTouches, lastRun, lastBound⟩ := right.erase _ (left.valid data valid)
  exact ⟨1 + beforeTouches.length + afterTouches.length,
    ⟨middle.erase, beforeTouches, afterTouches, i, firstRun, key, lastRun, rfl⟩, by omega⟩

/-- A shared request execution projects to the existing multifinger request
model, with the same input and endpoint states and no larger total charge. -/
theorem Requests.Execution.erase {α : Type} {fingers : Nat} {s t : State α fingers} {xs : List Nat}
    {events : List (Cells.Event α)} {cost : Nat} (run : Requests.Execution s xs t events cost)
    (data : Nat → α) (valid : s.Valid data) :
    ∃ work, Multifinger.Execution s.erase xs t.erase work ∧ work ≤ cost := by
  induction run generalizing data with
  | nil => exact ⟨0, .nil, Nat.le_refl _⟩
  | cons visit _ ih =>
    obtain ⟨firstCost, firstRun, firstBound⟩ := visit.erase data valid
    obtain ⟨lastCost, lastRun, lastBound⟩ := ih _ (visit.trace.valid data valid)
    exact ⟨firstCost + lastCost, .cons firstRun lastRun, by omega⟩

end RotationBST.TreeBuffer.Shared
