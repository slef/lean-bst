module

public import RotationBST.Models.RealWorld.Compiler.Boundaries

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs)
variable {w f r l : Nat}

/-- Each source tick is implemented inside one program with constant overhead. -/
theorem tick_simulation (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    {out : Option Multifinger.Opcode} (hw : 0 < w) (image : Image s t)
    (transition : tick p s = some (u, out)) :
    ∃ v n, n ≤ 19 ∧ Runs (compile p) t v n ∧ Image u v := by
  obtain ⟨c, rep, hc, hr, hq, hs, hp⟩ := image
  have im : Image s t := ⟨c, rep, hc, hr, hq, hs, hp⟩
  cases hpc : s.pc with
  | none => simp [tick, hpc] at transition
  | some pc =>
    have ht : t.pc = address pc := by simpa [hpc, location] using hp
    have he : eval (p.code pc) s = some (u, out) := by simpa [tick, hpc] using transition
    cases source : p.code pc with
    | literal dst value next =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst (BitVec.ofNat w value)
        (.op (.literal value) (userReg dst) (zeroReg r) (zeroReg r))
        (by simp [source, block]) (by simp [source, block]) (by simp) rfl rfl
      exact ⟨v, 2, by decide, run, img⟩
    | copy dst src next =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst (s.regs src)
        (.moveData (userReg dst) (userReg src))
        (by simp [source, block]) (by simp [source, block]) (by simp) rfl
        (by simp [Instr.effect, hr])
      exact ⟨v, 2, by decide, run, img⟩
    | add dst a b next =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst (s.regs a + s.regs b)
        (.op .add (userReg dst) (userReg a) (userReg b))
        (by simp [source, block]) (by simp [source, block]) (by simp) rfl
        (by simp [Instr.effect, hr])
      exact ⟨v, 2, by decide, run, img⟩
    | sub dst a b next =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst (s.regs a - s.regs b)
        (.op .sub (userReg dst) (userReg a) (userReg b))
        (by simp [source, block]) (by simp [source, block]) (by simp) rfl
        (by simp [Instr.effect, hr])
      exact ⟨v, 2, by decide, run, img⟩
    | branch a b yes no =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      exact branch_block p pc yes no a b im ht source
    | query dst next =>
      simp only [source, eval] at he
      rcases he with ⟨rfl, rfl⟩
      obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst s.request
        (.moveData (userReg dst) (queryReg r))
        (by simp [source, block]) (by simp [source, block]) (by simp) rfl
        (by simp [Instr.effect, hq])
      exact ⟨v, 2, by decide, run, img⟩
    | bst op next =>
      simp only [source, eval] at he
      cases hm : LabelledCursor.perform op s.cursor with
      | none => simp [hm] at he
      | some d =>
        simp [hm] at he
        rcases he with ⟨rfl, rfl⟩
        exact bst_block p pc next op im ht source hm
    | load dst i next =>
      rcases c with ⟨tree, cs⟩
      cases tree with
      | nil => exact False.elim (rep.nonempty rfl)
      | node a x b =>
        have read : s.cursor.read = some (decode x) := by rw [hc]; rfl
        have hd : t.deref 0 = some (Linked.node (Linked.root a) (Linked.root b) (Linked.parent cs) x) := by
          simp [Cslib.PointerMachine.State.deref, rep.cursor, Linked.root, rep.focus.1]
        simp [source, eval, read] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst ((decode x).data i)
          (.loadData (userReg dst) (field i) 0)
          (by simp [source, block]) (by simp [source, block]) (by simp) rfl
          (by simp [Instr.effect, hd, Linked.node, decode])
        exact ⟨v, 2, by decide, run, img⟩
    | key dst next =>
      rcases c with ⟨tree, cs⟩
      cases tree with
      | nil => exact False.elim (rep.nonempty rfl)
      | node a x b =>
        have read : s.cursor.read = some (decode x) := by rw [hc]; rfl
        have hd : t.deref 0 = some (Linked.node (Linked.root a) (Linked.root b) (Linked.parent cs) x) := by
          simp [Cslib.PointerMachine.State.deref, rep.cursor, Linked.root, rep.focus.1]
        simp [source, eval, read] at he
        rcases he with ⟨rfl, rfl⟩
        obtain ⟨v, run, img⟩ := set_reg_block p pc next im ht dst (decode x).key
          (.loadData (userReg dst) 0 0)
          (by simp [source, block]) (by simp [source, block]) (by simp) rfl
          (by simp [Instr.effect, hd, Linked.node, decode])
        exact ⟨v, 2, by decide, run, img⟩
    | store i src next =>
      rcases c with ⟨tree, cs⟩
      cases tree with
      | nil => exact False.elim (rep.nonempty rfl)
      | node a x b =>
        simp [source, eval, hc, LabelledCursor.Config.map, LabelledTree.map,
          LabelledCursor.Config.read, LabelledCursor.Config.write] at he
        rcases he with ⟨rfl, rfl⟩
        let instr : Opcode w f r := .storeData (field i) 0 (userReg src)
        have data : (instr.effect t).data = t.data := by
          simp [instr, Instr.effect, Cslib.PointerMachine.State.modify, rep.cursor, Linked.root]
        refine ⟨{ instr.effect t with pc := address next }, 2, by decide,
          scalar_block p pc next t instr ht (by simp [source, block, instr])
            (by simp [source, block]) (by simp [instr]) rfl,
          ⟨.node a (updateLabel x (field i) (t.data (userReg src))) b, cs⟩,
          realizes_control (store_realizes rep i (userReg src)) rfl rfl, ?_, ?_, ?_, ?_, rfl⟩
        · simp [LabelledCursor.Config.map, LabelledTree.map, decode_update, hr]
        · simpa [data] using hr
        · simpa [data] using hq
        · simpa [data] using hs
    | mark next =>
      rcases c with ⟨tree, cs⟩
      cases tree with
      | nil => exact False.elim (rep.nonempty rfl)
      | node a x b =>
        have read : s.cursor.read = some (decode x) := by rw [hc]; rfl
        have hd : t.deref 0 = some (Linked.node (Linked.root a) (Linked.root b) (Linked.parent cs) x) := by
          simp [Cslib.PointerMachine.State.deref, rep.cursor, Linked.root, rep.focus.1]
        simp [source, eval, read] at he
        rcases he with ⟨key, rfl, rfl⟩
        obtain ⟨v, run, img⟩ := mark_block p pc next im ht source _ hd key
        exact ⟨v, 4, by decide, run, img⟩
    | finish =>
      simp [source, eval] at he
      rcases he with ⟨seen, rfl, rfl⟩
      obtain ⟨v, run, img⟩ := finish_block p pc im ht source seen hw
      exact ⟨v, 3, by decide, run, img⟩

end RotationBST.RealWorld.Compiler
