module

public import RotationBST.Models.RealWorld.Compiler.Metadata

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs step)
variable {w f r l : Nat}

theorem image_set_reg {s : State w f r l} {t : Target w f r} (h : Image s t)
    (dst : Fin r) (value : BitVec w) (next : Fin l) :
    Image { s with regs := Function.update s.regs dst value, pc := some next }
      { t.setData (userReg dst) value with pc := address next } := by
  obtain ⟨c, rep, hc, hr, hq, hs, _⟩ := h
  refine ⟨c, realizes_control rep rfl rfl, hc, ?_, ?_, ?_, rfl⟩
  · intro i
    simp [Cslib.PointerMachine.State.setData, Function.update_apply, hr]
  · simpa [Cslib.PointerMachine.State.setData, Ne.symm (user_ne_query dst)] using hq
  · simpa [Cslib.PointerMachine.State.setData, Ne.symm (user_ne_seen dst)] using hs

theorem image_jump {s : State w f r l} {t : Target w f r} (h : Image s t)
    (next : Option (Fin l)) :
    Image { s with pc := next } { t with pc := location next } := by
  obtain ⟨c, rep, hc, hr, hq, hs, _⟩ := h
  exact ⟨c, realizes_control rep rfl rfl, hc, hr, hq, hs, rfl⟩

theorem one (code : List (Opcode w f r)) (t : Target w f r) (i : Opcode w f r)
    (hi : code[t.pc]? = some i) (ne : i ≠ .halt) :
    Runs code t { i.effect t with pc := i.next t } 1 :=
  .single (Cslib.PointerMachine.step_eq_some_iff.mpr ⟨i, hi, ne, rfl⟩)

/-- A scalar instruction followed by an explicit continuation jump. -/
theorem scalar_block (p : Machine f r l) (pc next : Fin l) (t : Target w f r)
    (i : Opcode w f r) (ht : t.pc = address pc)
    (hi : (block (address pc) (p.code pc))[0]? = some i)
    (hj : (block (w := w) (address pc) (p.code pc))[1]? = some (.goto (address next)))
    (ne : i ≠ .halt) (hn : i.next t = t.pc + 1) :
    Runs (compile p) t { i.effect t with pc := address next } 2 := by
  have h0 : (compile p)[t.pc]? = some i := by
    rw [ht]
    simpa [hi] using block_lookup (w := w) p pc 0 (by decide)
  have h1 : (compile (w := w) p)[i.next t]? = some (.goto (address next)) := by
    rw [hn, ht]
    simpa [hj] using block_lookup (w := w) p pc 1 (by decide)
  refine .tail _ _ _ _ (one _ _ _ h0 ne) ?_
  exact Cslib.PointerMachine.step_eq_some_iff.mpr ⟨.goto (address next), h1, by simp, rfl⟩

/-- Instantiate the scalar block when its data effect has already been identified. -/
theorem set_reg_block (p : Machine f r l) (pc next : Fin l)
    {s : State w f r l} {t : Target w f r} (image : Image s t) (ht : t.pc = address pc)
    (dst : Fin r) (value : BitVec w) (i : Opcode w f r)
    (hi : (block (address pc) (p.code pc))[0]? = some i)
    (hj : (block (w := w) (address pc) (p.code pc))[1]? = some (.goto (address next)))
    (ne : i ≠ .halt) (hn : i.next t = t.pc + 1)
    (he : i.effect t = t.setData (userReg dst) value) :
    ∃ v, Runs (compile p) t v 2 ∧
      Image { s with regs := Function.update s.regs dst value, pc := some next } v := by
  refine ⟨_, ?_, image_set_reg image dst value next⟩
  simpa [he] using scalar_block p pc next t i ht hi hj ne hn

end RotationBST.RealWorld.Compiler
