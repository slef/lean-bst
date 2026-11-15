module

public import RotationBST.Models.RealWorld.Compiler.Online

@[expose] public section
namespace RotationBST.RealWorld.Compiler
open Cslib.PointerMachine (Instr Runs)
variable {w f r l : Nat}

def noAlloc : Opcode w f r → Prop
  | .create _ => False
  | _ => True

theorem block_noAlloc (base : Nat) (i : Instruction f r l) :
    ∀ op ∈ block (w := w) base i, noAlloc op := by
  cases i <;> simp [block, noAlloc]
  rename_i op next
  cases op <;> simp [Linked.program, Linked.move, Linked.rotate, relocate]

theorem getD_noAlloc (ops : List (Opcode w f r)) (good : ∀ i ∈ ops, noAlloc i)
    (k exit : Nat) : noAlloc ((ops[k]?).getD (.goto exit)) := by
  cases h : ops[k]? with
  | none => trivial
  | some i => exact good i (List.mem_of_getElem? h)

theorem compile_noAlloc (p : Machine f r l) : ∀ i ∈ compile (w := w) p, noAlloc i := by
  intro i hi
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hi
  dsimp
  split
  · exact getD_noAlloc _ (block_noAlloc _ _) _ _
  · split
    · trivial
    · split
      · trivial
      · split <;> trivial

theorem noAlloc_length {i : Opcode w f r} (h : noAlloc i) (s : Target w f r) :
    (i.effect s).heap.length = s.heap.length := by
  cases i <;> simp_all only [noAlloc]
  all_goals simp [Instr.effect, Cslib.PointerMachine.State.setPtr,
    Cslib.PointerMachine.State.setData, Cslib.PointerMachine.State.modify, Option.elim]
  all_goals split <;> simp

theorem storage_preserved (p : Machine f r l) {s t : Target w f r} {n : Nat}
    (run : Runs (compile p) s t n) : t.heap.length = s.heap.length := by
  induction run with
  | refl => rfl
  | tail _ _ _ _ hs ih =>
    obtain ⟨i, hi, _, rfl⟩ := Cslib.PointerMachine.step_eq_some_iff.mp hs
    exact (noAlloc_length (compile_noAlloc p i (List.mem_of_getElem? hi)) _).trans ih

theorem compile_length (p : Machine f r l) : (compile (w := w) p).length = 24 * l + 4 := by
  simp [compile, boundary, stride]

/-- The source proportional-time certificate transfers with explicit constants. -/
theorem proportional_response (p : Machine f r l) {s u : State w f r l} {t : Target w f r}
    {key : BitVec w} {time cost constant : Nat} (hw : 0 < w) (image : Image s t)
    (response : RealWorld.Responds p s key u time cost) (bound : time ≤ constant * (cost + 1)) :
    ∃ v actual, actual ≤ (19 * constant + 3) * (cost + 1) ∧
      Responds p t key v actual ∧ Image u v := by
  obtain ⟨v, actual, ha, resp, im⟩ := response_simulation p hw image response
  refine ⟨v, actual, ?_, resp, im⟩
  have scaled := Nat.mul_le_mul_left 19 bound
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_one] at *
  omega

end RotationBST.RealWorld.Compiler
