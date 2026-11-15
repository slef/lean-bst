module

public import RotationBST.Models.RealWorld.Linked.Navigation
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

@[expose] public section
namespace RotationBST.RealWorld.Linked
open Cslib.PointerMachine (Instr Runs Executes step)
variable {w e regs : Nat}

/-- Bounded evaluator results are backed by actual charged execution, including halt. -/
theorem run_executes (code : List (Instruction w e regs)) (fuel : Nat) (s : State w e regs)
    (h : code[(run code fuel s).pc]? = some .halt) :
    ∃ time ≤ fuel + 1, Executes code s (run code fuel s) time := by
  induction fuel generalizing s with
  | zero => exact ⟨1, by omega, 0, .refl s, h, rfl⟩
  | succ n ih =>
    cases hs : step code s with
    | none =>
      simp only [run, hs] at h ⊢
      exact ⟨1, by omega, 0, .refl s, h, rfl⟩
    | some t =>
      simp only [run, hs] at h ⊢
      obtain ⟨time, bound, k, steps, halt, eq⟩ := ih t h
      refine ⟨time + 1, by omega, k + 1, ?_, halt, by omega⟩
      exact .head _ _ _ _ hs steps

theorem run_step (code : List (Instruction w e regs)) (n : Nat) (s : State w e regs)
    (i : Instruction w e regs) (h : code[s.pc]? = some i) (ne : i ≠ .halt) :
    run code (n + 1) s = run code n { i.effect s with pc := i.next s } := by
  simp only [run, step, h]

theorem run_halt (code : List (Instruction w e regs)) (n : Nat) (s : State w e regs)
    (h : code[s.pc]? = some .halt) : run code n s = s := by
  cases n <;> simp [run, step, h]

theorem rotate_progress (s : State w e regs) (side other : Fin 3) (bound : s.pc < 17) :
    ∃ t, step (rotate side other) s = some t ∧ s.pc < t.pc ∧ t.pc ≤ 17 := by
  generalize hp : s.pc = n at *
  interval_cases n <;> simp [step, rotate, hp, Instr.next]
  all_goals split_ifs <;> simp_all

theorem rotate_halts_aux (side other : Fin 3) (fuel : Nat) (s : State w e regs)
    (bound : s.pc ≤ 17) (enough : 17 - s.pc < fuel) :
    (rotate (w := w) (e := e) (regs := regs) side other)[(run (rotate side other) fuel s).pc]? = some .halt := by
  induction fuel generalizing s with
  | zero => omega
  | succ n ih =>
    by_cases done : s.pc = 17
    · rw [run_halt _ _ _ (by simp [rotate, done])]
      simp [rotate, done]
    · obtain ⟨t, hs, ht, hb⟩ := rotate_progress s side other (by omega)
      simp only [run, hs]
      exact ih t hb (by omega)

theorem rotate_halts (s : State w e regs) (side other : Fin 3) :
    (rotate (w := w) (e := e) (regs := regs) side other)[(run (rotate side other) 18 (start s)).pc]? = some .halt :=
  rotate_halts_aux side other 18 (start s) (by simp [start]) (by simp [start])

theorem rotate_time (s : State w e regs) (side other : Fin 3) :
    ∃ time ≤ 19, Executes (rotate side other) (start s)
      (run (rotate side other) 18 (start s)) time :=
  run_executes _ _ _ (rotate_halts s side other)

end RotationBST.RealWorld.Linked
