module

public import RotationBST.Algorithms.Combination.Refinement.Abstract
public import RotationBST.Structures.TreeBuffer.Nodes.Layout
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.ComboRefinement
open Combo TreeBuffer

private def leaf : Tree := .node .nil .nil
private def saved : Tree := .node leaf leaf
private def cursor (state : Fin 4) : Pointer.Config :=
  match state.val with
  | 0 => ⟨saved, []⟩
  | 1 => ⟨leaf, [.left leaf]⟩
  | 2 => ⟨.node .nil (.node .nil leaf), []⟩
  | _ => ⟨.node .nil leaf, [.right .nil]⟩
private def opcode (state : Fin 4) : Multifinger.Opcode :=
  match state.val with
  | 0 => .downLeft
  | 1 => .rotateLeftChild
  | 2 => .downRight
  | _ => .rotateRightChild
private def next (state : Fin 4) : Fin 4 := ⟨(state.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
private def worker : Controller.Worker (Fin 4) :=
  ⟨fun _ => 0, fun _ state _ => (next state, state.val % 2 == 1)⟩

-- A real opcode cycle visits a child, rotates it to the root, visits the
-- opposite child, and rotates back. Its two-step requests can be interrupted.
-- This checks instruction refinement; no all-keys service contract is assumed.
private def model : Refinement.WorkerModel worker saved where
  cursor := fun _ state => cursor state
  Ready := fun _ _ => True
  instruction := fun _ state _ => some (opcode state)
  restart_ready := fun _ => trivial
  restart_cursor := fun _ => rfl
  size := by intro side state _; fin_cases state <;> rfl
  step_ready := fun _ _ _ _ _ => trivial
  step_cursor := by intro side state x _ _; fin_cases state <;> rfl

private def codes : Nat → Nat := Snapshot.CellIO.payload saved
private def actual : Shared.State Nat 2 := ⟨Nodes.label codes saved 0, fun i => if i = 0 then 1 else 2⟩
private theorem represented : Refinement.Represents model codes actual false 0 := by
  refine ⟨trivial, ⟨by decide, by decide, ?_⟩, rfl, rfl⟩
  intro i
  fin_cases i <;> decide

private theorem interrupted : Controller.AttemptRun worker false 0 1 0 ⟨1, 0, false⟩ 1 :=
  .more rfl .exhausted

example : ∃ final events cost, Shared.Trace actual final events cost ∧ Refinement.Represents model codes final false 1 ∧
    Snapshot.Streaming.Refinement.Reads codes events ∧ final.position 1 = actual.position 1 ∧ cost ≤ 15 := by
  simpa only [Nat.mul_one] using Refinement.Results.attempt model interrupted (by decide) codes actual represented

-- The first request consumes two steps. The next exhausts its last unit
-- after moving down-right, so the snapshot loader must return from a nonroot
-- finger before restoring and retrying on the other worker.
private theorem execution : Controller.Execution worker 3 169 (Controller.initial worker 3)
    [0, 0] ⟨true, 2, 1⟩ 174 1 := .cons (by decide) (.cons (by decide) .nil)

example : ∃ final events cost, Shared.Trace actual final events cost ∧ Refinement.Represents model codes final true 2 ∧
    Snapshot.Streaming.Refinement.Reads codes events ∧ cost ≤ 2610 :=
  Refinement.Results.execution model execution (by intro x member; simp at member; subst x; decide)
    (by decide) codes (fun _ _ => rfl) actual represented

private theorem access (side : Bool) (state : Fin 4) (x : Nat) :
    ∃ final cost, Worker.Access worker side state x final cost ∧ cost ≤ 2 := by
  fin_cases state
  · exact ⟨2, 2, .more rfl (.done rfl), by decide⟩
  · exact ⟨2, 1, .done rfl, by decide⟩
  · exact ⟨0, 2, .more rfl (.done rfl), by decide⟩
  · exact ⟨0, 1, .done rfl, by decide⟩

private theorem requests (side : Bool) (state : Fin 4) (xs : List Nat) :
    ∃ final cost, Worker.Requests worker side state xs final cost ∧ cost ≤ 2 * xs.length := by
  induction xs generalizing state with
  | nil => exact ⟨state, 0, .nil, by decide⟩
  | cons x xs ih =>
    obtain ⟨middle, firstCost, first, firstBound⟩ := access side state x
    obtain ⟨final, lastCost, last, lastBound⟩ := ih middle
    exact ⟨final, firstCost + lastCost, .cons first last, by simp only [List.length_cons]; omega⟩

private def charges : Analysis.Charges := fun _ _ _ => 2
private theorem total (side : Bool) (xs : List Nat) : Analysis.total charges side xs = 2 * (xs.length : ℝ) := by
  simp [Analysis.total, Analysis.mass, charges, mul_comm]
private theorem well : Analysis.WellBehaved worker saved.size 3 1 1 charges := by
  constructor
  · intro side xs i; norm_num [charges]
  · intro side earlier state spent _ _ x _
    obtain ⟨final, cost, run, bound⟩ := access side state x
    exact ⟨final, cost, run, by omega⟩
  · intro side xs _
    obtain ⟨final, cost, run, bound⟩ := requests side (worker.restart side) xs
    have realBound : (cost : ℝ) ≤ 2 * (xs.length : ℝ) := by exact_mod_cast bound
    exact ⟨final, cost, run, by rw [total]; linarith⟩
  · intro side xs _ lo hi ordered inside
    have length : (Analysis.segment xs lo hi).length = hi - lo := by
      simp only [Analysis.segment, List.length_take, List.length_drop]
      omega
    rw [total, length]
    simp [Analysis.mass, charges, mul_comm]

-- Startup is included from arbitrary routing words and snapshot cells, then
-- the actual initialized state feeds the shared-node controller trace.
example (fields : Nat → IntervalMetadata.Bounds) (data : Nat → Nat) :
    ∃ ready snapshotData saveEvents saveCost final events cost endState work switches,
      Snapshot.Startup.Execution saved saved.size fields data ready saveEvents saveCost ∧
      Snapshot.CellIO.Stored saved snapshotData ∧
      Controller.run worker 6 171 (Controller.initial worker 6) [0, 0] = some (endState, work) ∧
      Controller.Execution worker 6 171 (Controller.initial worker 6) [0, 0] endState work switches ∧
      Shared.Trace ready final events cost ∧ Refinement.Represents model snapshotData final endState.side endState.workerState ∧
      Snapshot.Streaming.Refinement.Reads snapshotData events ∧ ((saveCost + cost : Nat) : ℝ) ≤ 18309 := by
  have result := Refinement.Results.startup model well (by decide) (by decide) fields data [0, 0]
    (by intro x member; simp at member; subst x; decide)
  convert result using 1; norm_num [Analysis.budget, saved, leaf, Tree.size, total]

end RotationBST.Tests.ComboRefinement
