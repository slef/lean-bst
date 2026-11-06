module

public import RotationBST.Algorithms.Combination.Worker.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Controller.Attempts
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Controller

theorem AttemptRun.computed {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work) :
    attempt worker side x fuel s = result := by
  induction run with
  | exhausted => rfl
  | done instruction => simp only [attempt, instruction, ↓reduceIte]
  | more instruction _ ih => simpa only [attempt, instruction, Bool.false_eq_true, ↓reduceIte] using ih

/-- Successful attempts stop at the same worker state and use the same work,
regardless of their available budgets. -/
theorem AttemptRun.completed_unique {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work otherFuel otherWork : Nat}
    {s : σ} {result other : Attempt σ} (first : AttemptRun worker side x fuel s result work)
    (finished : result.done = true) (second : AttemptRun worker side x otherFuel s other otherWork)
    (alsoFinished : other.done = true) : result.state = other.state ∧ work = otherWork := by
  induction first generalizing otherFuel otherWork other with
  | exhausted => contradiction
  | done instruction =>
    cases second with
    | exhausted => contradiction
    | done next =>
      have same := Prod.mk.inj (instruction.symm.trans next)
      exact ⟨same.1, rfl⟩
    | more next _ => have bad := congrArg Prod.snd (instruction.symm.trans next); contradiction
  | more instruction tail ih =>
    cases second with
    | exhausted => contradiction
    | done next => have bad := congrArg Prod.snd (instruction.symm.trans next); contradiction
    | more next rest =>
      have same := (Prod.mk.inj (instruction.symm.trans next)).1
      subst_vars
      obtain ⟨state, cost⟩ := ih finished rest alsoFinished
      exact ⟨state, by omega⟩

/-- A failed attempt is strictly shorter than any complete execution of that
same request from the same state. In particular, exact-boundary completion is
never misclassified as exhaustion. -/
theorem AttemptRun.failed_lt_complete {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work otherFuel otherWork : Nat}
    {s : σ} {result other : Attempt σ} (first : AttemptRun worker side x fuel s result work)
    (failed : result.done = false) (second : AttemptRun worker side x otherFuel s other otherWork)
    (finished : other.done = true) : fuel < otherWork := by
  induction first generalizing otherFuel otherWork other with
  | exhausted => exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (second.positive finished)
  | done => contradiction
  | more instruction tail ih =>
    cases second with
    | exhausted => contradiction
    | done next => have bad := congrArg Prod.snd (instruction.symm.trans next); contradiction
    | more next rest =>
      have same := (Prod.mk.inj (instruction.symm.trans next)).1
      subst_vars
      have shorter := ih failed rest finished
      omega

/-- Remove unused fuel from a successful attempt, producing a standalone
complete worker access with the exact same instructions and cost. -/
theorem AttemptRun.to_access {σ : Type} {worker : Worker σ} {side : Bool} {x fuel work : Nat}
    {s : σ} {result : Attempt σ} (run : AttemptRun worker side x fuel s result work)
    (finished : result.done = true) : Worker.Access worker side s x result.state work := by
  induction run with
  | exhausted => contradiction
  | done instruction => exact AttemptRun.done (fuel := 0) instruction
  | more instruction _ ih =>
    simpa only [Worker.Access, Nat.add_comm] using AttemptRun.more instruction (ih finished)

end RotationBST.Combo.Controller
