module

public import RotationBST.Algorithms.Combination.Worker.Replay.Definitions.Abstract
public import RotationBST.Algorithms.Combination.Worker.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
public import RotationBST.Models.Pointer.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Combo.Worker.Replay
open Multifinger

variable {σ : Type} {saved : Tree} (planner : Planner σ saved)

theorem running_access (side : Bool) (x : Nat) (next : σ) (current : Pointer.Config) (ops : List Opcode)
    (legal : replay ops current = some ⟨planner.tree side next, []⟩) :
    Worker.Access (worker planner) side (.running next current ops) x (.boundary next) (ops.length + 1) := by
  induction ops generalizing current with
  | nil => exact .done rfl
  | cons op ops ih =>
    obtain ⟨moved, first, rest⟩ := Option.bind_eq_some_iff.mp legal
    have tail := ih moved rest
    have ran : Controller.AttemptRun (worker planner) side x (ops.length + 1 + 1)
        (.running next current (op :: ops)) ⟨.boundary next, 0, true⟩ (1 + (ops.length + 1)) :=
      .more (by simp [worker, step, first]) tail
    simpa only [Worker.Access, List.length_cons, Nat.add_comm 1 (ops.length + 1)] using ran

theorem access (side : Bool) (state : σ) (x : Nat)
    (size : (planner.tree side state).size = saved.size) (valid : x < saved.size) :
    Worker.Access (worker planner) side (.boundary state) x (.boundary (planner.plan side state x).1)
      ((planner.plan side state x).2.length + 2) := by
  have tail := running_access planner side x _ _ _ (planner.legal side state x size valid)
  have ran := Controller.AttemptRun.more (worker := worker planner) (side := side) (x := x)
    (s := .boundary state) (by rfl) tail
  simpa only [Worker.Access, Nat.add_comm 1, Nat.add_assoc] using ran

theorem plan_size (side : Bool) (state : σ) (x : Nat)
    (size : (planner.tree side state).size = saved.size) (valid : x < saved.size) :
    (planner.tree side (planner.plan side state x).1).size = saved.size := by
  obtain ⟨_, _, shapes⟩ := (Multifinger.Replay.Results.physical (planner.legal side state x size valid)).rotations
  exact shapes.size_eq.symm.trans size

theorem run_size (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    (planner.tree side (run planner side state xs).1).size = saved.size := by
  induction xs generalizing state with
  | nil => exact size
  | cons x xs ih =>
    exact ih _ (plan_size planner side state x size (valid x (by simp)))
      (by intro y member; exact valid y (by simp [member]))

theorem requests (side : Bool) (state : σ) (xs : List Nat)
    (size : (planner.tree side state).size = saved.size) (valid : ∀ x ∈ xs, x < saved.size) :
    Worker.Requests (worker planner) side (.boundary state) xs (.boundary (run planner side state xs).1)
      (run planner side state xs).2 := by
  induction xs generalizing state with
  | nil => exact .nil
  | cons x xs ih =>
    exact .cons (access planner side state x size (valid x (by simp)))
      (ih _ (plan_size planner side state x size (valid x (by simp))) (by intro y member; exact valid y (by simp [member])))

theorem request_boundary {side : Bool} {state : State σ}
    (boundary : Refinement.Visits.Boundary (worker planner) saved.size side state) :
    ∃ original, state = .boundary original ∧ (planner.tree side original).size = saved.size := by
  obtain ⟨earlier, spent, ran, valid⟩ := boundary
  have standard := requests planner side (planner.initial side) earlier
    (congrArg Tree.size (planner.initial_tree side)) valid
  obtain ⟨same, _⟩ := Worker.Results.Requests.unique ran standard
  exact ⟨_, same, run_size planner side (planner.initial side) earlier
    (congrArg Tree.size (planner.initial_tree side)) valid⟩

end RotationBST.Combo.Worker.Replay
