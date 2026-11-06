module

public import RotationBST.Structures.TreeBuffer.Snapshot.Controller.Normalization
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Controller
open Multifinger

theorem tick_replay {s t : State} {op : Option Opcode} (transition : tick s = some (op, t)) :
    replay op.toList s.cursor = some t.cursor := by
  cases decision : choose s with
  | none => simp only [tick, decision, Option.bind_none, reduceCtorEq] at transition
  | some choice =>
    rcases choice with ⟨action, mode, depth⟩
    cases action with
    | none =>
      simp only [tick, decision, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at transition
      obtain ⟨rfl, rfl⟩ := transition
      rfl
    | some instruction =>
      cases physical : perform instruction s.cursor with
      | none => simp only [tick, decision, Option.bind_some, physical, Option.map_none, reduceCtorEq] at transition
      | some cursor =>
        simp only [tick, decision, Option.bind_some, physical, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at transition
        obtain ⟨rfl, rfl⟩ := transition
        simp only [Option.toList_some, replay, physical, Option.bind_some]

theorem Run.replay {s t : State} {ops : List Opcode} (run : Run s ops t) :
    Multifinger.replay ops s.cursor = some t.cursor := by
  induction run with
  | refl => rfl
  | silent transition _ ih =>
    have same := tick_replay transition
    simp only [Option.toList_none, Multifinger.replay, Option.some.injEq] at same
    simpa only [same] using ih
  | instruction transition _ ih =>
    have first := tick_replay transition
    simp only [Option.toList_some, Multifinger.replay, Option.bind_fun_some] at first
    simp only [Multifinger.replay, first, Option.bind_some, ih]

/-- While a left child is being promoted, the physical cursor has descended one
extra level. Otherwise the depth counter is exactly the zipper depth. -/
def Aligned (s : State) : Prop :=
  s.depth + (if s.mode = .promote then 1 else 0) = s.cursor.context.length

theorem tick_aligned {s t : State} {op : Option Opcode} (transition : tick s = some (op, t))
    (aligned : Aligned s) : Aligned t := by
  rcases s with ⟨⟨focus, cs⟩, depth, mode⟩
  cases mode with
  | scan =>
    cases focus with
    | nil =>
      simp only [tick, choose, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at transition
      obtain ⟨rfl, rfl⟩ := transition
      simpa [Aligned] using aligned
    | node l r =>
      cases l with
      | nil =>
        cases r with
        | nil =>
          simp only [tick, choose, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at transition
          obtain ⟨rfl, rfl⟩ := transition
          simpa [Aligned] using aligned
        | node a b =>
          simp only [tick, choose, Option.bind_some, perform, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at transition
          obtain ⟨rfl, rfl⟩ := transition
          simp_all [Aligned]
      | node a b =>
        simp only [tick, choose, Option.bind_some, perform, Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at transition
        obtain ⟨rfl, rfl⟩ := transition
        simp_all [Aligned]
  | promote =>
    cases focus with
    | nil => simp [tick, choose, perform] at transition
    | node a b =>
      cases cs with
      | nil => simp [tick, choose, perform] at transition
      | cons frame cs =>
        cases frame with
        | right l => simp [tick, choose, perform] at transition
        | left r =>
          simp only [tick, choose, Option.bind_some, perform, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at transition
          obtain ⟨rfl, rfl⟩ := transition
          simp_all [Aligned]
  | ascend =>
    cases depth with
    | zero => simp [tick, choose] at transition
    | succ depth =>
      cases focus with
      | nil => simp [tick, choose, perform] at transition
      | node a b =>
        cases cs with
        | nil => simp [tick, choose, perform] at transition
        | cons frame cs =>
          cases frame with
          | left r => simp [tick, choose, perform] at transition
          | right l =>
            simp only [tick, choose, Option.bind_some, perform, Option.map_some, Option.some.injEq,
              Prod.mk.injEq] at transition
            obtain ⟨rfl, rfl⟩ := transition
            simp_all [Aligned]

theorem Run.aligned {s t : State} {ops : List Opcode} (run : Run s ops t) (aligned : Aligned s) : Aligned t := by
  induction run with
  | refl => exact aligned
  | silent step _ ih => exact ih (tick_aligned step aligned)
  | instruction step _ ih => exact ih (tick_aligned step aligned)

private theorem context_size (cs : List Pointer.Frame) (t : Tree) :
    cs.length + t.size ≤ (Pointer.plug cs t).size := by
  induction cs generalizing t with
  | nil => simp [Pointer.plug]
  | cons frame cs ih =>
    cases frame with
    | left r => have bound := ih (.node t r); simp only [List.length_cons, Pointer.plug, Tree.size] at *; omega
    | right l => have bound := ih (.node l t); simp only [List.length_cons, Pointer.plug, Tree.size] at *; omega

/-- On every legal prefix from the root, the sole counter is bounded by the
number of nodes. Thus the controller needs no recursion stack or saved shape. -/
theorem counter_focus_bound (t : Tree) {s : State} {ops : List Opcode}
    (run : Run ⟨⟨t, []⟩, 0, .scan⟩ ops s) : s.depth + s.cursor.focus.size ≤ t.size := by
  have aligned := run.aligned (by simp [Aligned])
  obtain ⟨_, _, rotations⟩ := (replay_trace run.replay).rotations
  have size := rotations.size_eq
  have context := context_size s.cursor.context s.cursor.focus
  change s.cursor.context.length + s.cursor.focus.size ≤ s.cursor.tree.size at context
  change t.size = s.cursor.tree.size at size
  unfold Aligned at aligned
  omega

theorem counter_bound (t : Tree) {s : State} {ops : List Opcode}
    (run : Run ⟨⟨t, []⟩, 0, .scan⟩ ops s) : s.depth ≤ t.size := by
  have bound := counter_focus_bound t run
  omega

end RotationBST.TreeBuffer.Snapshot.Controller
