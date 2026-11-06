module

public import RotationBST.Structures.TreeBuffer.Shared.Execution
public import RotationBST.Models.Pointer.Walk.Basic

@[expose] public section
namespace RotationBST.TreeBuffer.Shared

/-- Navigation-only walks lift with their exact one-unit cost per edge.
No routing search or reset of any other persistent finger is inserted. -/
theorem walk {α : Type} {fingers : Nat} {a b : Pointer.Config} {cost : Nat}
    (path : Pointer.Walk a b cost) (data : Nat → α) (s : State α fingers)
    (valid : s.Valid data) (i : Fin fingers) (tree : s.tree.erase = a.tree)
    (key : a.key? = some (s.position i)) :
    ∃ t, Trace s t [] cost ∧ t.tree.erase = b.tree ∧ b.key? = some (t.position i) ∧
      (∀ j, j ≠ i → t.position j = s.position j) := by
  induction path generalizing s with
  | refl => exact ⟨s, .refl, tree, key, fun _ _ => rfl⟩
  | @step a middle b cost move path ih =>
    obtain ⟨op, operation⟩ := Multifinger.perform_complete move.step
    obtain ⟨nextKey, atNext⟩ := move.step.keys_exist.2
    obtain ⟨next, first, shape, positions⟩ := move_exists s data valid i op a middle tree.symm key operation move nextKey atNext
    obtain ⟨last, rest, finalTree, finalKey, inactive⟩ := ih next (first.valid data valid) shape
      (by simpa only [positions, Function.update_self] using atNext)
    refine ⟨last, ?_, finalTree, finalKey, ?_⟩
    · simpa only [Option.toList_none, List.nil_append, Nat.add_comm 1 cost] using first.trace.append rest
    · intro j different
      rw [inactive j different, positions, Function.update_of_ne different]

private theorem context_size (cs : List Pointer.Frame) (t : Tree) :
    cs.length + t.size ≤ (Pointer.plug cs t).size := by
  induction cs generalizing t with
  | nil => simp [Pointer.plug]
  | cons frame cs ih =>
    cases frame with
    | left r =>
      have bound := ih (.node t r)
      simp only [List.length_cons, Pointer.plug, Tree.size] at bound ⊢
      omega
    | right l =>
      have bound := ih (.node l t)
      simp only [List.length_cons, Pointer.plug, Tree.size] at bound ⊢
      omega

/-- Return one persistent finger to the current root using actual parent
moves. Its exact charge is its depth, bounded by the number of nodes. -/
theorem to_root {α : Type} {fingers : Nat} (data : Nat → α) (s : State α fingers)
    (valid : s.Valid data) (i : Fin fingers) :
    ∃ t cost, Trace s t [] cost ∧ t.Valid data ∧ t.tree.erase = s.tree.erase ∧
      (Pointer.Config.mk s.tree.erase []).key? = some (t.position i) ∧
      (∀ j, j ≠ i → t.position j = s.position j) ∧
      cost = Tree.depth s.tree.erase (s.position i) ∧ cost ≤ s.tree.erase.size := by
  obtain ⟨l, r, cs, tree, key, depth⟩ := Pointer.search_location s.tree.erase (s.position i) (valid.2.2 i)
  have atKey : (Pointer.Config.mk (.node l r) cs).key? = some (s.position i) := congrArg some key
  obtain ⟨t, trace, shape, atRoot, inactive⟩ :=
    walk (Pointer.walk_ascend cs l r) data s valid i tree.symm atKey
  refine ⟨t, cs.length, trace, trace.valid data valid, ?_, ?_, inactive, depth, ?_⟩
  · simpa only [Pointer.Config.tree, Pointer.plug, tree] using shape
  · simpa only [tree] using atRoot
  · have bound := context_size cs (.node l r)
    rw [tree] at bound
    omega

end RotationBST.TreeBuffer.Shared
