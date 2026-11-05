module

public import RotationBST.Models.Multifinger.Proofs

@[expose] public section
namespace RotationBST.Multifinger

/-- A persistent ordinary cursor is a one-finger execution with exactly the
same instruction count and endpoint keys. Intermediate touched keys are retained. -/
theorem pointer_trace {a b : Pointer.Config} {k x y : Nat} (run : Pointer.Trace a b k)
    (first : a.key? = some x) (last : b.key? = some y) :
    ∃ touches : List Nat, touches.length = k ∧
      Trace (⟨a.tree, fun _ : Fin 1 => x⟩ : State 1) touches ⟨b.tree, fun _ => y⟩ := by
  induction run generalizing x with
  | refl =>
    have eq := Option.some.inj (first.symm.trans last)
    subst y
    exact ⟨[], rfl, .refl⟩
  | step instruction rest ih =>
    obtain ⟨key, touched⟩ := instruction.keys_exist.2
    obtain ⟨touches, length, tail⟩ := ih touched last
    refine ⟨key :: touches, ?_, .step (pointer_step instruction first touched) tail⟩
    simp only [List.length_cons, length]

end RotationBST.Multifinger
