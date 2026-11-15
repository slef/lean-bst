module

public import RotationBST.Models.RealWorld.Definitions.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.RealWorld

/-- Erasing scalar work leaves either no tree change or one legal BST step. -/
theorem eval_physical {w f r l : Nat} {i : Instruction f r l}
    {s t : State w f r l} {out : Option Multifinger.Opcode}
    (h : eval i s = some (t, out)) :
    Pointer.Trace s.cursor.erase t.cursor.erase out.toList.length := by
  cases i with
  | literal | copy | add | sub | branch | query =>
      simp only [eval, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .refl
  | load | key =>
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨node, _, rfl, rfl⟩ := h
      exact .refl
  | store =>
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨node, _, cursor, written, rfl, rfl⟩ := h
      change Pointer.Trace s.cursor.erase cursor.erase 0
      rw [LabelledCursor.Results.write_erase written]
      exact .refl
  | bst =>
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨cursor, moved, rfl, rfl⟩ := h
      exact .step (LabelledCursor.Results.perform_physical moved) .refl
  | mark =>
      simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨node, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .refl
      · contradiction
  | finish =>
      simp only [eval] at h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .refl
      · contradiction

 theorem tick_physical {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {out : Option Multifinger.Opcode}
    (h : tick p s = some (t, out)) :
    Pointer.Trace s.cursor.erase t.cursor.erase out.toList.length := by
  unfold tick at h
  cases hp : s.pc with
  | none => simp [hp] at h
  | some pc => exact eval_physical (by simpa [hp] using h)

 theorem trace_append {s t u : Pointer.Config} {a b : Nat}
    (h : Pointer.Trace s t a) (k : Pointer.Trace t u b) : Pointer.Trace s u (a + b) := by
  induction h with
  | refl => simpa using k
  | step step _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Pointer.Trace.step step (ih k)

 theorem run_physical {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {time cost : Nat} (h : Run p s t time cost) :
    Pointer.Trace s.cursor.erase t.cursor.erase cost := by
  induction h with
  | nil => exact .refl
  | cons step _ ih =>
      simpa [Nat.add_comm] using trace_append (tick_physical step) ih

 theorem cost_le_time {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {time cost : Nat} (h : Run p s t time cost) : cost ≤ time := by
  induction h with
  | nil => omega
  | @cons s t u time cost out step rest ih => cases out <;> simp_all; omega

 theorem transition_deterministic {w f r l : Nat} (p : Machine f r l)
    {s t u : State w f r l} {event : Event w}
    (h : (lts p).Tr s event t) (k : (lts p).Tr s event u) : t = u := by
  cases event <;> simp only [lts] at h k
  · exact Option.some.inj (h.symm.trans k)
  · exact congrArg Prod.fst (Option.some.inj (h.symm.trans k))

 theorem boundary_stuck {w f r l : Nat} (p : Machine f r l)
    (s : State w f r l) (h : s.pc = none) : tick p s = none := by
  simp [tick, h]

/-- Two completed runs from the same state agree, including both costs. -/
 theorem completed_unique {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {time cost : Nat} (h : Run p s t time cost)
    (halt : t.pc = none) : ∀ {u a b}, Run p s u a b → u.pc = none →
      t = u ∧ time = a ∧ cost = b := by
  induction h with
  | nil =>
      intro u a b other stop
      cases other with
      | nil => exact ⟨rfl, rfl, rfl⟩
      | cons step rest => simp [boundary_stuck _ _ halt] at step
  | @cons s v t time cost out step rest ih =>
      intro u a b other stop
      cases other with
      | nil => simp [boundary_stuck _ _ stop] at step
      | cons step' rest' =>
          have eq := Option.some.inj (step.symm.trans step')
          cases eq
          obtain ⟨ht, ha, hb⟩ := ih halt rest' stop
          exact ⟨ht, by omega, by omega⟩

 theorem response_unique {w f r l : Nat} {p : Machine f r l}
    {s t u : State w f r l} {x : BitVec w} {a b c d : Nat}
    (h : Responds p s x t a b) (k : Responds p s x u c d) :
    t = u ∧ a = c ∧ b = d := by
  obtain ⟨start, hs, run, halt⟩ := h
  obtain ⟨start', hs', run', halt'⟩ := k
  have eq := Option.some.inj (hs.symm.trans hs')
  subst start'
  exact completed_unique run halt run' halt'

/-- Causality: a completed request prefix has a unique retained state and costs.
Any continuation must therefore start from that same state. -/
 theorem execution_unique {w f r l : Nat} {p : Machine f r l}
    {s t : State w f r l} {xs : List (BitVec w)} {a b : Nat}
    (h : Execution p s xs t a b) : ∀ {u c d}, Execution p s xs u c d →
      t = u ∧ a = c ∧ b = d := by
  induction h with
  | nil => intro u c d k; cases k; exact ⟨rfl, rfl, rfl⟩
  | cons response rest ih =>
      intro u c d k
      cases k with
      | cons response' rest' =>
          obtain ⟨eq, ha, hb⟩ := response_unique response response'
          subst eq
          obtain ⟨ht, hc, hd⟩ := ih rest'
          exact ⟨ht, by omega, by omega⟩

 theorem execution_append {w f r l : Nat} {p : Machine f r l}
    {s t u : State w f r l} {xs ys : List (BitVec w)} {a b c d : Nat}
    (h : Execution p s xs t a b) (k : Execution p t ys u c d) :
    Execution p s (xs ++ ys) u (a + c) (b + d) := by
  induction h with
  | nil => simpa using k
  | cons response rest ih =>
      simpa [Nat.add_assoc] using Execution.cons response (ih k)

end RotationBST.RealWorld
