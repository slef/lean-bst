module

public import RotationBST.Models.RealWorld.Compiler.Definitions.Abstract

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs Executes step)
variable {w f r : Nat}

def shift (base : Nat) (s : Target w f r) : Target w f r := { s with pc := base + s.pc }

theorem relocate_effect (base exit : Nat) (i : Opcode w f r) (s : Target w f r) :
    (relocate base exit i).effect (shift base s) = shift base (i.effect s) := by
  cases i <;> simp [relocate, Instr.effect, shift, Cslib.PointerMachine.State.setPtr,
    Cslib.PointerMachine.State.setData, Cslib.PointerMachine.State.deref,
    Cslib.PointerMachine.State.modify, Option.elim]
  all_goals split <;> simp_all only

theorem relocate_next (base exit : Nat) (i : Opcode w f r) (s : Target w f r)
    (ne : i ≠ .halt) :
    (relocate base exit i).next (shift base s) = base + i.next s := by
  cases i <;> simp_all [relocate, Instr.next, shift, Nat.add_assoc]
  all_goals split <;> rfl

/-- A block embedding includes its halt, which becomes the continuation jump. -/
def Contains (target source : List (Opcode w f r)) (base exit : Nat) : Prop :=
  ∀ pc i, source[pc]? = some i → target[base + pc]? = some (relocate base exit i)

theorem relocate_step {target source : List (Opcode w f r)} {base exit : Nat}
    (code : Contains target source base exit) {s t : Target w f r}
    (h : step source s = some t) : step target (shift base s) = some (shift base t) := by
  obtain ⟨i, hi, ne, rfl⟩ := Cslib.PointerMachine.step_eq_some_iff.mp h
  apply Cslib.PointerMachine.step_eq_some_iff.mpr
  refine ⟨relocate base exit i, code _ _ hi, ?_, ?_⟩
  · cases i <;> simp [relocate]
  · rw [relocate_effect, relocate_next _ _ _ _ ne]
    rfl

theorem relocate_runs {target source : List (Opcode w f r)} {base exit : Nat}
    (code : Contains target source base exit) {s t : Target w f r} {n : Nat}
    (h : Runs source s t n) : Runs target (shift base s) (shift base t) n := by
  induction h with
  | refl => exact .refl _
  | tail _ _ _ _ hs ih => exact .tail _ _ _ _ ih (relocate_step code hs)

/-- Replacing the final halt by a jump preserves the total charged count. -/
theorem relocate_executes {target source : List (Opcode w f r)} {base exit : Nat}
    (code : Contains target source base exit) {s t : Target w f r} {n : Nat}
    (h : Executes source s t n) :
    Runs target (shift base s) { t with pc := exit } n := by
  obtain ⟨k, run, halt, rfl⟩ := h
  refine .tail _ _ _ _ (relocate_runs code run) ?_
  simp [step, shift, code _ _ halt, relocate, Instr.effect, Instr.next]

end RotationBST.RealWorld.Compiler
