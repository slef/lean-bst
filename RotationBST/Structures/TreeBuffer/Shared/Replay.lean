module

public import RotationBST.Structures.TreeBuffer.Shared.Execution
public import RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Lift a complete pointer program at one persistent finger. Its opcode list
is a proof witness; the controller may emit it incrementally. Inactive fingers
retain their node identities throughout the run. -/
theorem replay {α : Type} {fingers : Nat} (ops : List Multifinger.Opcode) (data : Nat → α)
    (s : State α fingers) (valid : s.Valid data) (i : Fin fingers) (a b : Pointer.Config)
    (tree : s.tree.erase = a.tree) (key : a.key? = some (s.position i))
    (execution : Multifinger.replay ops a = some b) :
    ∃ t cost, Trace s t [] cost ∧ t.tree.erase = b.tree ∧ b.key? = some (t.position i) ∧
      (∀ j, j ≠ i → t.position j = s.position j) ∧ cost ≤ 15 * ops.length := by
  induction ops generalizing s a with
  | nil =>
    cases Option.some.inj execution
    exact ⟨s, 0, .refl, tree, key, fun _ _ => rfl, Nat.le_refl _⟩
  | cons op ops ih =>
    obtain ⟨next, instruction, rest⟩ : ∃ next, Multifinger.perform op a = some next ∧
        Multifinger.replay ops next = some b := by
      simpa only [Multifinger.replay, Option.bind_eq_some_iff] using execution
    obtain ⟨nextKey, atNext⟩ := (Multifinger.perform_sound instruction).keys_exist.2
    obtain ⟨middle, firstCost, first, charged, shape, positions⟩ :=
      execute_exists s data valid i op a next tree.symm key instruction nextKey atNext
    have middleValid : middle.Valid data := first.valid data valid
    obtain ⟨final, restCost, tail, finalShape, finalKey, inactive, bound⟩ :=
      ih middle middleValid next shape (by simpa only [positions, Function.update_self] using atNext) rest
    refine ⟨final, firstCost + restCost, first.trace.append tail, finalShape, finalKey, ?_, ?_⟩
    · intro j different
      rw [inactive j different, positions, Function.update_of_ne different]
    · simp only [List.length_cons]
      omega

end RotationBST.TreeBuffer.Shared
