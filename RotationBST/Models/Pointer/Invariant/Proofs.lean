module

public import RotationBST.Models.Pointer.Invariant.Definitions.Abstract
public import RotationBST.Models.Pointer.Navigation
public import RotationBST.Models.Multifinger.Program.Replay.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Pointer.TraceWithin

variable {P Q : Tree → Prop} {a b c : Config} {k m : Nat}

theorem trace (h : TraceWithin P a b k) : Trace a b k := by
  induction h with
  | refl => exact .refl
  | step _ step _ ih => exact .step step ih

theorem start (h : TraceWithin P a b k) : P a.tree := by
  cases h with
  | refl holds => exact holds
  | step holds => exact holds

theorem finish (h : TraceWithin P a b k) : P b.tree := by
  induction h with
  | refl holds => exact holds
  | step _ _ _ ih => exact ih

theorem weaken (h : TraceWithin P a b k) (imp : ∀ t, P t → Q t) : TraceWithin Q a b k := by
  induction h with
  | refl holds => exact .refl (imp _ holds)
  | step holds step _ ih => exact .step (imp _ holds) step ih

theorem append (h : TraceWithin P a b k) (g : TraceWithin P b c m) : TraceWithin P a c (k + m) := by
  induction h with
  | refl => simpa using g
  | step holds step _ ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 m] using TraceWithin.step holds step (ih g)

/-- A contextual invariant is transported without charging extra work. -/
theorem under (cs : List Frame) (h : TraceWithin (fun t => P (plug cs t)) a b k) :
    TraceWithin P (a.under cs) (b.under cs) k := by
  induction h with
  | refl holds =>
    apply TraceWithin.refl
    simpa only [Config.under, Config.tree, plug_append] using holds
  | step holds step _ ih =>
    apply TraceWithin.step _ (step.under cs) ih
    simpa only [Config.under, Config.tree, plug_append] using holds

/-- Recording retains the invariant at every physical prefix, and the
remaining suffix still replays to the same endpoint. -/
theorem record (h : TraceWithin P a b k) :
    ∃ ops : List Multifinger.Opcode, ops.length = k ∧ Multifinger.replay ops a = some b ∧
      ∀ cut, ∃ middle, Multifinger.replay (ops.take cut) a = some middle ∧
        Multifinger.replay (ops.drop cut) middle = some b ∧ P middle.tree := by
  induction h with
  | @refl a holds => exact ⟨[], rfl, rfl, fun _ => ⟨a, by simp [Multifinger.replay], by simp [Multifinger.replay], holds⟩⟩
  | @step a b c cost holds step tail ih =>
    obtain ⟨op, performed⟩ := Multifinger.perform_complete step
    obtain ⟨ops, length, replay, prefixes⟩ := ih
    refine ⟨op :: ops, by simp [length], ?_, ?_⟩
    · simp only [Multifinger.replay, performed, Option.bind_some, replay]
    · intro cut
      cases cut with
      | zero =>
        refine ⟨a, rfl, ?_, holds⟩
        simpa only [List.drop_zero, Multifinger.replay, performed, Option.bind_some] using replay
      | succ cut =>
        obtain ⟨middle, first, last, bound⟩ := prefixes cut
        refine ⟨middle, ?_, last, bound⟩
        simpa only [List.take_succ_cons, Multifinger.replay, performed, Option.bind_some] using first

theorem descend (cs : List Frame) (l r : Tree) (holds : P (plug cs (.node l r))) :
    TraceWithin P ⟨plug cs (.node l r), []⟩ ⟨.node l r, cs⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl holds
  | cons frame cs ih =>
    cases frame with
    | left b => exact (ih (.node l r) b holds).append (.step holds .downLeft (.refl holds))
    | right a => exact (ih a (.node l r) holds).append (.step holds .downRight (.refl holds))

theorem ascend (cs : List Frame) (l r : Tree) (holds : P (plug cs (.node l r))) :
    TraceWithin P ⟨.node l r, cs⟩ ⟨plug cs (.node l r), []⟩ cs.length := by
  induction cs generalizing l r with
  | nil => exact .refl holds
  | cons frame cs ih =>
    cases frame with
    | left b => exact .step holds .upLeft (ih (.node l r) b holds)
    | right a => exact .step holds .upRight (ih a (.node l r) holds)

theorem inContext {s t : Tree} (cs : List Frame)
    (h : TraceWithin (fun u => P (plug cs u)) ⟨s, []⟩ ⟨t, []⟩ k)
    (hs : s ≠ .nil) (ht : t ≠ .nil) :
    TraceWithin P ⟨plug cs s, []⟩ ⟨plug cs t, []⟩ (cs.length + k + cs.length) := by
  cases s with
  | nil => exact False.elim (hs rfl)
  | node a b =>
    cases t with
    | nil => exact False.elim (ht rfl)
    | node c d => exact ((descend cs a b h.start).append (h.under cs)).append (ascend cs c d h.finish)

end RotationBST.Pointer.TraceWithin
