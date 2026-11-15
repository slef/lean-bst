module

public import RotationBST.Models.RealWorld.Compiler.Scalar

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs Executes)
variable {w f r l : Nat}

def keepsData : Opcode w f r → Prop
  | .moveData .. | .loadData .. | .op .. => False
  | _ => True

theorem effect_keepsData {i : Opcode w f r} (h : keepsData i) (s : Target w f r) :
    (i.effect s).data = s.data := by
  cases i <;> simp_all only [keepsData]
  all_goals simp [Instr.effect, Cslib.PointerMachine.State.setPtr,
    Cslib.PointerMachine.State.modify, Option.elim]
  all_goals split <;> rfl

theorem primitive_keepsData (op : Multifinger.Opcode) :
    ∀ i ∈ Linked.program (w := w) (e := f) (regs := r + 4) op, keepsData i := by
  cases op <;> simp [Linked.program, Linked.move, Linked.rotate, keepsData]

theorem runs_keepsData {code : List (Opcode w f r)}
    (good : ∀ i ∈ code, keepsData i) {s t : Target w f r} {n : Nat} (h : Runs code s t n) :
    t.data = s.data := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ hs ih =>
    obtain ⟨i, hi, _, rfl⟩ := Cslib.PointerMachine.step_eq_some_iff.mp hs
    exact (effect_keepsData (good i (List.mem_of_getElem? hi)) _).trans ih

/-- The certified primitive runs inside the single compiled controller;
its continuation jump is included in the same constant instruction bound. -/
theorem bst_block (p : Machine f r l) (pc next : Fin l) (op : Multifinger.Opcode)
    {s : State w f r l} {t : Target w f r} {cursor : LabelledCursor.Config (Node w f)}
    (image : Image s t) (ht : t.pc = address pc) (source : p.code pc = .bst op next)
    (legal : LabelledCursor.perform op s.cursor = some cursor) :
    ∃ v n, n ≤ 19 ∧ Runs (compile p) t v n ∧ Image { s with cursor := cursor, pc := some next } v := by
  obtain ⟨c, rep, hc, hr, hq, hs, _⟩ := image
  have map := LabelledCursor.perform_map decode op c
  rw [← hc, legal] at map
  obtain ⟨d, step, hd⟩ := Option.map_eq_some_iff.mp map
  obtain ⟨v, n, bound, exec, rep', _⟩ := Linked.primitive rep step
  have data : v.data = t.data := by
    simpa only [Linked.start] using runs_keepsData (s := Linked.start t) (primitive_keepsData op) exec.choose_spec.1
  refine ⟨{ v with pc := address next }, n, bound, ?_, d,
    realizes_control rep' rfl rfl, hd.symm, ?_, ?_, ?_, rfl⟩
  · simpa [shift, Linked.start, ← ht] using relocate_executes (primitive_contains p pc next op source) exec
  · simpa [data] using hr
  · simpa [data] using hq
  · simpa [data] using hs

end RotationBST.RealWorld.Compiler
