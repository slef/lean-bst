module

public import RotationBST.Structures.TreeBuffer.Shared.Matching

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Every existing pointer instruction lifts to the shared-node model. Plain
navigation costs one; a rotation includes all metadata work and costs fifteen. -/
theorem execute_exists {α : Type} {fingers : Nat} (s : State α fingers) (data : Nat → α)
    (valid : s.Valid data) (i : Fin fingers) (op : Multifinger.Opcode) (a b : Pointer.Config)
    (tree : a.tree = s.tree.erase) (key : a.key? = some (s.position i))
    (execution : Multifinger.perform op a = some b) (nextKey : Nat) (atNext : b.key? = some nextKey) :
    ∃ t cost, Step s i t none cost ∧ cost ≤ 15 ∧ t.tree.erase = b.tree ∧
      t.position = Function.update s.position i nextKey := by
  have physical := Multifinger.perform_sound execution
  cases physical with
  | downLeft =>
    obtain ⟨t, step, shape, positions⟩ := move_exists s data valid i op _ _ tree key execution .downLeft nextKey atNext
    exact ⟨t, 1, step, by decide, shape, positions⟩
  | downRight =>
    obtain ⟨t, step, shape, positions⟩ := move_exists s data valid i op _ _ tree key execution .downRight nextKey atNext
    exact ⟨t, 1, step, by decide, shape, positions⟩
  | upLeft =>
    obtain ⟨t, step, shape, positions⟩ := move_exists s data valid i op _ _ tree key execution .upLeft nextKey atNext
    exact ⟨t, 1, step, by decide, shape, positions⟩
  | upRight =>
    obtain ⟨t, step, shape, positions⟩ := move_exists s data valid i op _ _ tree key execution .upRight nextKey atNext
    exact ⟨t, 1, step, by decide, shape, positions⟩
  | rotateLeftChild =>
    obtain ⟨t, step, shape, positions⟩ := rotate_exists s data valid i .left _ _ tree key rfl
    have same : nextKey = s.position i := by
      simp only [Pointer.Config.key?, Pointer.offset, Option.some.injEq] at key atNext
      omega
    refine ⟨t, 15, step, le_rfl, shape, ?_⟩
    simpa only [same, Function.update_eq_self] using positions
  | rotateRightChild =>
    obtain ⟨t, step, shape, positions⟩ := rotate_exists s data valid i .right _ _ tree key rfl
    have same : nextKey = s.position i := by
      simp only [Pointer.Config.key?, Pointer.offset, Tree.size, Option.some.injEq] at key atNext
      omega
    refine ⟨t, 15, step, le_rfl, shape, ?_⟩
    simpa only [same, Function.update_eq_self] using positions

theorem Step.trace {α : Type} {fingers : Nat} {s t : State α fingers} {i : Fin fingers}
    {event : Option (Cells.Event α)} {cost : Nat} (step : Step s i t event cost) :
    Trace s t event.toList cost := by
  simpa only [List.append_nil, Nat.add_zero] using Trace.step step Trace.refl

theorem Trace.append {α : Type} {fingers : Nat} {s t u : State α fingers} {first last : List (Cells.Event α)}
    {cost rest : Nat} (left : Trace s t first cost) (right : Trace t u last rest) :
    Trace s u (first ++ last) (cost + rest) := by
  induction left with
  | refl => simpa only [List.nil_append, Nat.zero_add] using right
  | step step _ ih => simpa only [List.append_assoc, Nat.add_assoc] using Trace.step step (ih right)

end RotationBST.TreeBuffer.Shared
