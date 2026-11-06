module

public import RotationBST.Structures.TreeBuffer.Snapshot.Definitions.Abstract
public import RotationBST.Models.Multifinger.Program.Replay.Basic
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot
open Multifinger

theorem vine_size (n : Nat) : (vine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [vine, Tree.size, ih, Nat.add_comm]

theorem vine_nonempty (n : Nat) (positive : 0 < n) : vine n ≠ .nil := by
  cases n with
  | zero => omega
  | succ n => simp [vine]

theorem work_le (t : Tree) : work t ≤ 2 * t.size := by
  induction t with
  | nil => simp [work, Tree.size]
  | node l r _ ih => simp only [work, Tree.size]; omega

/-- The same opcode list works in every ancestor context and leaves the cursor
at the normalized subtree's root. Its length counts all down/up instructions. -/
theorem recordFuel_spec (fuel : Nat) (t : Tree) (enough : work t ≤ fuel) (cs : List Pointer.Frame) :
    replay (recordFuel fuel t) ⟨t, cs⟩ = some ⟨vine t.size, cs⟩ ∧
      (recordFuel fuel t).length ≤ 2 * work t := by
  induction fuel generalizing t cs with
  | zero =>
    cases t with
    | nil => exact ⟨rfl, by simp [recordFuel, work]⟩
    | node l r => simp only [work] at enough; omega
  | succ fuel ih =>
    cases t with
    | nil => exact ⟨rfl, by simp [recordFuel, work]⟩
    | node l r =>
      cases l with
      | nil =>
        cases r with
        | nil => exact ⟨rfl, by simp [recordFuel, work]⟩
        | node a b =>
          have remaining : work (.node a b) ≤ fuel := by simp only [work, Tree.size] at enough ⊢; omega
          obtain ⟨run, bound⟩ := ih (.node a b) remaining (.right .nil :: cs)
          have nonempty := vine_nonempty (Tree.node a b).size (by simp only [Tree.size]; omega)
          cases canonical : vine (Tree.node a b).size with
          | nil => exact False.elim (nonempty canonical)
          | node c d =>
            constructor
            · simp only [recordFuel, replay, perform, Option.bind_some]
              rw [replay_append, run, Option.bind_some, canonical]
              simp only [replay, perform, Option.bind_some]
              have outer : (Tree.node .nil (.node a b)).size = (Tree.node a b).size + 1 := by simp only [Tree.size]; omega
              rw [outer, vine, canonical]
            · simp only [recordFuel, List.length_cons, List.length_append, List.length_nil, work, Tree.size] at bound ⊢
              omega
      | node a b =>
        have remaining : work (.node a (.node b r)) ≤ fuel := by simp only [work, Tree.size] at enough ⊢; omega
        obtain ⟨run, bound⟩ := ih (.node a (.node b r)) remaining cs
        constructor
        · simp only [recordFuel, replay, perform, Option.bind_some]
          have size : (Tree.node a (.node b r)).size = (Tree.node (.node a b) r).size := by simp only [Tree.size]; omega
          simpa only [size] using run
        · simp only [recordFuel, List.length_cons, work, Tree.size] at bound ⊢
          omega

theorem record_replay (t : Tree) (cs : List Pointer.Frame) :
    replay (record t) ⟨t, cs⟩ = some ⟨vine t.size, cs⟩ :=
  (recordFuel_spec (work t) t le_rfl cs).1

theorem record_length (t : Tree) : (record t).length ≤ 4 * t.size := by
  have bound := (recordFuel_spec (work t) t le_rfl []).2
  have workBound := work_le t
  change (record t).length ≤ _ at bound
  omega

end RotationBST.TreeBuffer.Snapshot
