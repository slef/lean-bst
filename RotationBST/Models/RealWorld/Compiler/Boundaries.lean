module

public import RotationBST.Models.RealWorld.Compiler.Branch

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs)
variable {w f r l : Nat}

theorem mark_block (p : Machine f r l) (pc next : Fin l)
    {s : State w f r l} {t : Target w f r} (image : Image s t) (ht : t.pc = address pc)
    (source : p.code pc = .mark next)
    (record : Linked.Record w f (r + 4)) (read : t.deref 0 = some record)
    (key : record.data 0 = s.request) :
    ∃ v, Runs (compile p) t v 4 ∧ Image { s with seen := true, pc := some next } v := by
  obtain ⟨c, rep, hc, hr, hq, hs, hp⟩ := image
  have im : Image s t := ⟨c, rep, hc, hr, hq, hs, hp⟩
  let v1 : Target w f r := { t.setData (tempReg r) s.request with pc := address pc + 1 }
  let v2 : Target w f r := { v1 with pc := address pc + 3 }
  let v3 : Target w f r := { v2.setData (seenReg r) (flag w true) with pc := address pc + 4 }
  let v4 : Target w f r := { v3 with pc := address next }
  have h0 : (compile (w := w) p)[t.pc]? = some (.loadData (tempReg r) 0 0) := by
    rw [ht]; simpa [source, block] using block_lookup (w := w) p pc 0 (by decide)
  have h1 : (compile (w := w) p)[address pc + 1]? =
      some (.ifTest .eq (tempReg r) (queryReg r) (address pc + 3)) := by
    simpa [source, block] using block_lookup (w := w) p pc 1 (by decide)
  have h3 : (compile (w := w) p)[address pc + 3]? =
      some (.op (.literal 1) (seenReg r) (zeroReg r) (zeroReg r)) := by
    simpa [source, block] using block_lookup (w := w) p pc 3 (by decide)
  have h4 : (compile (w := w) p)[address pc + 4]? = some (.goto (address next)) := by
    simpa [source, block] using block_lookup (w := w) p pc 4 (by decide)
  have run1 : Runs (compile p) t v1 1 := by
    simpa [Instr.effect, Instr.next, read, key, ht, v1] using one (compile p) t _ h0 (by simp)
  have hq' := hq
  simp only [queryReg] at hq'
  have run2 : Runs (compile p) v1 v2 1 := by
    simpa [v1, v2, Instr.effect, Instr.next, Cslib.PointerMachine.State.setData,
      tempReg, queryReg, Fin.ext_iff, hq'] using one (compile p) v1 _ h1 (by simp)
  have run3 : Runs (compile p) v2 v3 1 := by
    simpa [v2, v3, Instr.effect, Instr.next, flag] using one (compile p) v2 _ h3 (by simp)
  have run4 : Runs (compile p) v3 v4 1 := by
    simpa [v3, v4, Instr.effect, Instr.next] using one (compile p) v3 _ h4 (by simp)
  refine ⟨v4, ((run1.trans run2).trans run3).trans run4, ?_⟩
  apply image_control (u := { s with seen := true, pc := some next }) (v := v4) im rfl rfl rfl
  · intro i
    simpa [v4, v3, v2, v1, Cslib.PointerMachine.State.setData,
      Ne.symm (user_ne_temp i), Ne.symm (user_ne_seen i)] using hr i
  · simpa [v4, v3, v2, v1, Cslib.PointerMachine.State.setData,
      queryReg, tempReg, seenReg, Fin.ext_iff] using hq
  · simp [v4, v3, Cslib.PointerMachine.State.setData]
  · rfl

theorem finish_block (p : Machine f r l) (pc : Fin l)
    {s : State w f r l} {t : Target w f r} (image : Image s t) (ht : t.pc = address pc)
    (source : p.code pc = .finish) (seen : s.seen = true) (hw : 0 < w) :
    ∃ v, Runs (compile p) t v 3 ∧ Image { s with pc := (none : Option (Fin l)) } v := by
  obtain ⟨c, rep, hc, hr, hq, hs, hp⟩ := image
  have im : Image s t := ⟨c, rep, hc, hr, hq, hs, hp⟩
  let v1 : Target w f r := { t.setData (zeroReg r) (BitVec.ofNat w 0) with pc := address pc + 1 }
  let v2 : Target w f r := { v1 with pc := address pc + 2 }
  let v3 : Target w f r := { v2 with pc := boundary l }
  have h0 : (compile (w := w) p)[t.pc]? =
      some (.op (.literal 0) (zeroReg r) (zeroReg r) (zeroReg r)) := by
    rw [ht]; simpa [source, block] using block_lookup (w := w) p pc 0 (by decide)
  have h1 : (compile (w := w) p)[address pc + 1]? =
      some (.ifTest .eq (seenReg r) (zeroReg r) (trap l)) := by
    simpa [source, block] using block_lookup (w := w) p pc 1 (by decide)
  have h2 : (compile (w := w) p)[address pc + 2]? = some (.goto (boundary l)) := by
    simpa [source, block] using block_lookup (w := w) p pc 2 (by decide)
  have nonzero : flag w true ≠ BitVec.ofNat w 0 := flag_ne_zero hw
  have run1 : Runs (compile p) t v1 1 := by
    simpa [Instr.effect, Instr.next, ht, v1] using one (compile p) t _ h0 (by simp)
  have hs' := hs
  simp only [seenReg, seen] at hs'
  have run2 : Runs (compile p) v1 v2 1 := by
    simpa [v1, v2, Instr.effect, Instr.next, Cslib.PointerMachine.State.setData,
      seenReg, zeroReg, Fin.ext_iff, hs', nonzero, Nat.add_assoc] using one (compile p) v1 _ h1 (by simp)
  have run3 : Runs (compile p) v2 v3 1 := by
    simpa [v2, v3, Instr.effect, Instr.next] using one (compile p) v2 _ h2 (by simp)
  refine ⟨v3, (run1.trans run2).trans run3, ?_⟩
  apply image_control (u := { s with pc := (none : Option (Fin l)) }) (v := v3) im rfl rfl rfl
  · intro i
    simpa [v3, v2, v1, Cslib.PointerMachine.State.setData, Ne.symm (user_ne_zero i)] using hr i
  · simpa [v3, v2, v1, Cslib.PointerMachine.State.setData, queryReg, zeroReg, Fin.ext_iff] using hq
  · simpa [v3, v2, v1, Cslib.PointerMachine.State.setData, seenReg, zeroReg, Fin.ext_iff] using hs
  · rfl

end RotationBST.RealWorld.Compiler
