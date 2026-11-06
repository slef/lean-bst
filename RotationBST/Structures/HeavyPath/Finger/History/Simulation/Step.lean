module

public import RotationBST.Structures.HeavyPath.Finger.History.Simulation.Definitions.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Down.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Up.Abstract
public import RotationBST.Structures.HeavyPath.Finger.History.Rotation.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Finger.History.Simulation
open LabelledCursor

/-- Uniform physical implementation of every legal source instruction. -/
theorem step_within {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.TraceWithin (fun t => t.size = s.pair.tree.size ∧
        ∀ x, Tree.depth t x ≤ 16 * Tree.depth s.pair.tree x + 96) ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  rcases c with ⟨focus, cs⟩
  cases focus with
  | nil => exact False.elim valid
  | node l key r =>
    change Valid weight cs l key r s at valid
    cases op with
    | downLeft =>
      cases l with
      | nil => simp [perform] at legal
      | node a x b =>
        simp only [perform, Option.some.injEq] at legal
        subst next
        obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Down.Results.downLeft_within valid
        exact ⟨after, cost, preserved, trace.weaken (by
          intro t h
          exact ⟨h.1, fun x => by have bound := h.2 x; omega⟩), by omega, by linarith⟩
    | downRight =>
      cases r with
      | nil => simp [perform] at legal
      | node a x b =>
        simp only [perform, Option.some.injEq] at legal
        subst next
        obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Down.Results.downRight_within valid
        exact ⟨after, cost, preserved, trace.weaken (by
          intro t h
          exact ⟨h.1, fun x => by have bound := h.2 x; omega⟩), by omega, by linarith⟩
    | upLeft =>
      cases cs with
      | nil => simp [perform] at legal
      | cons f cs =>
        cases f with
        | right sibling parent => simp [perform] at legal
        | left parent sibling =>
          simp only [perform, Option.some.injEq] at legal
          subst next
          obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Up.Results.upLeft_within valid
          exact ⟨after, cost, preserved, trace, bound, worst⟩
    | upRight =>
      cases cs with
      | nil => simp [perform] at legal
      | cons f cs =>
        cases f with
        | left parent sibling => simp [perform] at legal
        | right sibling parent =>
          simp only [perform, Option.some.injEq] at legal
          subst next
          obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Up.Results.upRight_within valid
          exact ⟨after, cost, preserved, trace, bound, worst⟩
    | rotateLeftChild =>
      cases cs with
      | nil => simp [perform] at legal
      | cons f cs =>
        cases f with
        | right sibling parent => simp [perform] at legal
        | left parent sibling =>
          simp only [perform, Option.some.injEq] at legal
          subst next
          obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Rotation.Results.rotateLeftChild_within valid
          exact ⟨after, cost, preserved, trace.weaken (by
            intro t h
            exact ⟨h.1, fun x => by have bound := h.2 x; omega⟩), by omega, by linarith⟩
    | rotateRightChild =>
      cases cs with
      | nil => simp [perform] at legal
      | cons f cs =>
        cases f with
        | left parent sibling => simp [perform] at legal
        | right sibling parent =>
          simp only [perform, Option.some.injEq] at legal
          subst next
          obtain ⟨after, cost, preserved, trace, bound, _, worst⟩ := Rotation.Results.rotateRightChild_within valid
          exact ⟨after, cost, preserved, trace.weaken (by
            intro t h
            exact ⟨h.1, fun x => by have bound := h.2 x; omega⟩), by omega, by linarith⟩

theorem step_bounded {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential ∧
      (cost : ℝ) ≤ 34 + 24 * Real.logb 2 s.pair.tree.size := by
  obtain ⟨after, cost, preserved, trace, bound, worst⟩ := step_within valid legal
  exact ⟨after, cost, preserved, trace.trace, bound, worst⟩

theorem step {α : Type} {weight : α → ℝ} {c next : Config α} {s : State α}
    {op : Multifinger.Opcode} (valid : ConfigValid weight c s)
    (legal : perform op c = some next) :
    ∃ (after : State α) (cost : Nat), ConfigValid weight next after ∧
      Pointer.Trace ⟨s.pair.tree, []⟩ ⟨after.pair.tree, []⟩ cost ∧
      cost + after.potential ≤ 62 + s.potential := by
  obtain ⟨after, cost, preserved, trace, amortized, _⟩ := step_bounded valid legal
  exact ⟨after, cost, preserved, trace, amortized⟩

end RotationBST.HeavyPath.Finger.History.Simulation
