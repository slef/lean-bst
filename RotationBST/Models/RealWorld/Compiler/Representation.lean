module

public import RotationBST.Models.RealWorld.Compiler.Code

@[expose] public section
namespace RotationBST.RealWorld.Compiler
variable {w f r l : Nat}

theorem realizes_control {s t : Target w f r} {c : Linked.Cursor w f}
    (h : Linked.Realizes s c) (hp : t.ptr = s.ptr) (hh : t.heap = s.heap) :
    Linked.Realizes t c := by
  exact ⟨by simpa only [Cslib.PointerMachine.State.Valid, hp, hh] using h.valid,
    hh ▸ h.focus, hh ▸ h.context, h.distinct, by simpa only [hh] using h.covers,
    h.ordered, hp ▸ h.cursor, hp ▸ h.rootReg, h.nonempty⟩

theorem image_control {s u : State w f r l} {t v : Target w f r}
    (h : Image s t) (hc : u.cursor = s.cursor)
    (hp : v.ptr = t.ptr) (hh : v.heap = t.heap)
    (hr : ∀ i, v.data (userReg i) = u.regs i)
    (hq : v.data (queryReg r) = u.request)
    (hs : v.data (seenReg r) = flag w u.seen) (pc : v.pc = location u.pc) : Image u v := by
  obtain ⟨c, rep, eq, _, _, _, _⟩ := h
  exact ⟨c, realizes_control rep hp hh, hc.trans eq, hr, hq, hs, pc⟩

@[simp] theorem userReg_injective {i j : Fin r} : userReg i = userReg j ↔ i = j := by
  simp [userReg, Fin.ext_iff]
@[simp] theorem user_ne_query (i : Fin r) : userReg i ≠ queryReg r := by
  simp [userReg, queryReg, Fin.ext_iff]; omega
@[simp] theorem user_ne_seen (i : Fin r) : userReg i ≠ seenReg r := by
  simp [userReg, seenReg, Fin.ext_iff]; omega
@[simp] theorem user_ne_temp (i : Fin r) : userReg i ≠ tempReg r := by
  simp [userReg, tempReg, Fin.ext_iff]; omega
@[simp] theorem user_ne_zero (i : Fin r) : userReg i ≠ zeroReg r := by
  simp [userReg, zeroReg, Fin.ext_iff]; omega

/-- Positive word width is needed to distinguish the stored visited bit. -/
theorem flag_ne_zero (hw : 0 < w) : flag w true ≠ flag w false := by
  simp [flag]
  have : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by decide)
  omega

end RotationBST.RealWorld.Compiler
