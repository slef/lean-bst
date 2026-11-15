module

public import RotationBST.Models.RealWorld.Compiler.Primitive

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs step)
variable {w f r l : Nat}

theorem branch_block (p : Machine f r l) (pc yes no : Fin l) (a b : Fin r)
    {s : State w f r l} {t : Target w f r} (image : Image s t) (ht : t.pc = address pc)
    (source : p.code pc = .branch a b yes no) :
    ∃ v n, n ≤ 19 ∧ Runs (compile p) t v n ∧
      Image { s with pc := some (if (s.regs a).toNat < (s.regs b).toNat then yes else no) } v := by
  obtain ⟨c, rep, hc, hr, hq, hs, hpc⟩ := image
  have im : Image s t := ⟨c, rep, hc, hr, hq, hs, hpc⟩
  have hi : (compile (w := w) p)[t.pc]? =
      some (.ifTest .lt (userReg a) (userReg b) (address yes)) := by
    rw [ht]
    simpa [source, block] using block_lookup (w := w) p pc 0 (by decide)
  by_cases cond : (s.regs a).toNat < (s.regs b).toNat
  · refine ⟨{ t with pc := address yes }, 1, by decide, ?_, ?_⟩
    · simpa [Instr.effect, Instr.next, hr, cond] using one (compile p) t _ hi (by simp)
    · simpa [cond, location] using image_jump im (some yes)
  · have h1 : (compile (w := w) p)[t.pc + 1]? = some (.goto (address no)) := by
      rw [ht]
      simpa [source, block] using block_lookup (w := w) p pc 1 (by decide)
    have first : Runs (compile p) t { t with pc := t.pc + 1 } 1 := by
      simpa [Instr.effect, Instr.next, hr, cond] using one (compile p) t _ hi (by simp)
    refine ⟨{ t with pc := address no }, 2, by decide, ?_, ?_⟩
    · exact .tail _ _ _ _ first
        (Cslib.PointerMachine.step_eq_some_iff.mpr ⟨.goto (address no), h1, by simp, rfl⟩)
    · simpa [cond, location] using image_jump im (some no)

end RotationBST.RealWorld.Compiler
