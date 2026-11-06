module

public import RotationBST.Structures.TreeBuffer.Shared.Requests.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Shared.Execution

@[expose] public section
namespace RotationBST.TreeBuffer.Shared.Requests

theorem Visit.trace {α : Type} {fingers : Nat} {s t : State α fingers} {x cost : Nat} {events : List (Cells.Event α)}
    (visit : Visit s t x events cost) : Trace s t events cost := by
  obtain ⟨middle, before, after, first, last, i, left, _, right, rfl, rfl⟩ := visit
  exact left.append right

theorem Visit.start {α : Type} {fingers : Nat} {s t : State α fingers} {x cost : Nat} {events : List (Cells.Event α)}
    (trace : Trace s t events cost) (i : Fin fingers) (key : s.position i = x) : Visit s t x events cost :=
  ⟨s, [], events, 0, cost, i, .refl, key, trace, rfl, by omega⟩

theorem Visit.finish {α : Type} {fingers : Nat} {s t : State α fingers} {x cost : Nat} {events : List (Cells.Event α)}
    (trace : Trace s t events cost) (i : Fin fingers) (key : t.position i = x) : Visit s t x events cost :=
  ⟨t, events, [], cost, 0, i, trace, key, .refl, by simp, by omega⟩

theorem Visit.prepend {α : Type} {fingers : Nat} {s t u : State α fingers} {x cost rest : Nat}
    {first last : List (Cells.Event α)} (trace : Trace s t first cost) (visit : Visit t u x last rest) :
    Visit s u x (first ++ last) (cost + rest) := by
  obtain ⟨middle, before, after, beforeCost, afterCost, i, left, key, right, rfl, rfl⟩ := visit
  exact ⟨middle, first ++ before, after, cost + beforeCost, afterCost, i, trace.append left, key, right,
    by simp only [List.append_assoc], by omega⟩

theorem Visit.append {α : Type} {fingers : Nat} {s t u : State α fingers} {x cost rest : Nat}
    {first last : List (Cells.Event α)} (visit : Visit s t x first cost) (trace : Trace t u last rest) :
    Visit s u x (first ++ last) (cost + rest) := by
  obtain ⟨middle, before, after, beforeCost, afterCost, i, left, key, right, rfl, rfl⟩ := visit
  exact ⟨middle, before, after ++ last, beforeCost, afterCost + rest, i, left, key, right.append trace,
    by simp only [List.append_assoc], by omega⟩

/-- Erasing request delimiters retains every charged shared operation. -/
theorem Execution.trace {α : Type} {fingers : Nat} {s t : State α fingers} {xs : List Nat}
    {events : List (Cells.Event α)} {cost : Nat} (run : Execution s xs t events cost) :
    ∃ work, Trace s t events work ∧ cost = xs.length + work := by
  induction run with
  | nil => exact ⟨0, .refl, rfl⟩
  | cons visit _ ih =>
    obtain ⟨work, trace, account⟩ := ih
    exact ⟨_, visit.trace.append trace, by simp only [List.length_cons]; omega⟩

end RotationBST.TreeBuffer.Shared.Requests
