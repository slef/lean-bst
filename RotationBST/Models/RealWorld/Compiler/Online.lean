module

public import RotationBST.Models.RealWorld.Compiler.Step

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs Executes)
variable {w f r l : Nat}

theorem run_simulation (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    {time cost : Nat} (hw : 0 < w) (image : Image s t) (run : Run p s u time cost) :
    ∃ v n, n ≤ 19 * time ∧ Runs (compile p) t v n ∧ Image u v := by
  induction run generalizing t with
  | nil => exact ⟨t, 0, by simp, .refl t, image⟩
  | cons step rest ih =>
    obtain ⟨mid, a, ha, first, im⟩ := tick_simulation p hw image step
    obtain ⟨v, b, hb, last, im'⟩ := ih im
    exact ⟨v, a + b, by omega, first.trans last, im'⟩

/-- External input only replaces the designated request register. The reset
of the visited flag and entry jump take two actual instructions. -/
theorem input_simulation (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    (image : Image s t) (key : BitVec w) (accepted : RealWorld.accept p key s = some u) :
    ∃ input v, accept (l := l) key t = some input ∧ Runs (compile p) input v 2 ∧ Image u v := by
  obtain ⟨c, rep, hc, hr, hq, hs, hp⟩ := image
  by_cases hpc : s.pc = none
  · simp [RealWorld.accept, hpc] at accepted
    subst u
    have ht : t.pc = boundary l := by simpa [hpc, location] using hp
    let input : Target w f r := { t.setData (queryReg r) key with pc := entry l }
    let v1 : Target w f r := { input.setData (seenReg r) (flag w false) with pc := entry l + 1 }
    let v2 : Target w f r := { v1 with pc := address p.entry }
    have first : Runs (compile p) input v1 1 := by
      simpa [input, v1, Instr.effect, Instr.next, flag] using
        one (compile p) input _ (entry_lookup p) (by simp)
    have last : Runs (compile p) v1 v2 1 := by
      simpa [v1, v2, Instr.effect, Instr.next] using
        one (compile p) v1 _ (entry_next_lookup p) (by simp)
    refine ⟨input, v2, by simp [accept, ht, input], first.trans last,
      c, realizes_control rep rfl rfl, hc, ?_, ?_, ?_, rfl⟩
    · intro i
      simpa [input, v1, v2, Cslib.PointerMachine.State.setData,
        Ne.symm (user_ne_seen i), Ne.symm (user_ne_query i)] using hr i
    · simp [input, v1, v2, Cslib.PointerMachine.State.setData, queryReg, seenReg, Fin.ext_iff]
    · simp [v1, v2, Cslib.PointerMachine.State.setData]
  · simp [RealWorld.accept, hpc] at accepted

/-- A whole successful source request is implemented by the single compiled
program, including entry bookkeeping and the final halt. -/
theorem response_simulation (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    {key : BitVec w} {time cost : Nat} (hw : 0 < w) (image : Image s t)
    (response : RealWorld.Responds p s key u time cost) :
    ∃ v actual, actual ≤ 19 * time + 3 ∧ Responds p t key v actual ∧ Image u v := by
  obtain ⟨sourceStart, accepted, sourceRun, finished⟩ := response
  obtain ⟨input, start, accepted', setup, im⟩ := input_simulation p image key accepted
  obtain ⟨v, n, hn, body, im'⟩ := run_simulation p hw im sourceRun
  have halt : (compile (w := w) p)[v.pc]? = some .halt := by
    obtain ⟨c, rep, hc, hr, hq, hs, hp⟩ := im'
    rw [hp, finished]
    exact boundary_lookup p
  exact ⟨v, n + 3, by omega, ⟨input, accepted', ⟨2 + n, setup.trans body, halt, by omega⟩⟩, im'⟩

theorem execution_simulation (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    {xs : List (BitVec w)} {time cost : Nat} (hw : 0 < w) (image : Image s t)
    (execution : RealWorld.Execution p s xs u time cost) :
    ∃ v actual, actual ≤ 19 * time + 3 * xs.length ∧ Execution p t xs v actual ∧ Image u v := by
  induction execution generalizing t with
  | nil => exact ⟨t, 0, by simp, .nil t, image⟩
  | cons response rest ih =>
    obtain ⟨mid, a, ha, first, im⟩ := response_simulation p hw image response
    obtain ⟨v, b, hb, last, im'⟩ := ih im
    refine ⟨v, a + b, ?_, .cons first last, im'⟩
    simp only [List.length_cons]
    omega

/-- The concrete request protocol has one endpoint and one charged time. -/
theorem response_unique {p : Machine f r l} {s t u : Target w f r} {key : BitVec w}
    {a b : Nat} (h : Responds p s key t a) (k : Responds p s key u b) :
    t = u ∧ a = b := by
  obtain ⟨input, hi, run⟩ := h
  obtain ⟨input', hk, run'⟩ := k
  have eq : input = input' := Option.some.inj (hi.symm.trans hk)
  subst input'
  exact run.unique run'

end RotationBST.RealWorld.Compiler
