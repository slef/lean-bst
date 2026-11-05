module

public import RotationBST.Structures.FingerHand.Packed.Suppression.Downward
public import RotationBST.Structures.FingerHand.Packed.Suppression.Upward
public import RotationBST.Models.Pointer.Location

@[expose] public section
namespace RotationBST.FingerHand.Hand

private theorem key_at_root (t : Tree) (cs : List Pointer.Frame) (nonempty : t ≠ .nil) :
    (Pointer.Config.mk t cs).key? = some (Pointer.offset cs + rootRank t) := by
  cases t with
  | nil => exact False.elim (nonempty rfl)
  | node => rfl

/-- A prepared actual instruction whose source key becomes obsolete has a
complete physical cleanup. Cursor uniqueness connects the actual instruction
to the newly located hand region, including when preparation changed its shape. -/
theorem cleanup_obsolete (h : Hand) (marks : Finset Nat) (a b : Pointer.Config) (x y : Nat)
    (valid : h.Valid) (tree : a.tree = h.reference)
    (key : a.key? = some x) (touched : b.key? = some y) (instruction : Pointer.Step a b)
    (oldMember : x ∈ (h.labels 0).inorder) (destination : y ∈ (h.labels 0).inorder)
    (marked : y ∈ marks) (canonical : h.labels 0 = compress (insert x marks) h.reference 0)
    (absent : x ∉ (compress marks h.reference 0).inorder) :
    ∃ (after : Hand) (k : Nat), after.Valid ∧ after.reference = h.reference ∧
      after.labels 0 = compress marks after.reference 0 ∧
      Suppress marks x (h.labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 134 + 10 * h.count + h.potential := by
  have unmarked := obsolete_unmarked h marks 0 x oldMember absent
  obtain ⟨fs, cs, d, l, r, rfl, referenceTree, referenceKey, depth⟩ := locate_reference h x oldMember
  have cursor : a = ⟨.node l.reference r.reference, cs ++ Context.referencePath fs⟩ :=
    Pointer.Config.ext_key (tree.trans referenceTree.symm) key referenceKey
  rw [cursor] at instruction
  have oldIndex : x = Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size := by
    have index := Option.some.inj referenceKey
    simp only [Pointer.offset_append] at index
    omega
  rw [oldIndex] at canonical absent ⊢
  suffices result : ∃ (after : Hand) (k : Nat), after.Valid ∧
      after.reference = (Context.plug fs (.node cs d l r)).reference ∧
      after.labels 0 = compress marks after.reference 0 ∧
      Suppress marks (Pointer.offset (Context.referencePath fs) + Pointer.offset cs + l.reference.size)
        ((Context.plug fs (.node cs d l r)).labels 0) (after.labels 0) ∧
      Pointer.Trace ⟨(Context.plug fs (.node cs d l r)).tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 134 + 10 * fs.length + (Context.plug fs (.node cs d l r)).potential by
    obtain ⟨after, k, afterValid, ref, normal, suppression, trace, cost⟩ := result
    exact ⟨after, k, afterValid, ref, normal, suppression, trace, by omega⟩
  rcases instruction.destination with same | ⟨nonempty, rfl⟩ | ⟨nonempty, rfl⟩ | ⟨f, anc, path, rfl⟩
  · have eq : y = x := Option.some.inj (touched.symm.trans (same.trans referenceKey))
    exact False.elim (unmarked (eq ▸ marked))
  · have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
    simp only [Pointer.offset, Pointer.offset_append] at index
    have eq : y = Pointer.offset (Context.referencePath fs) + Pointer.offset cs + rootRank l.reference := by omega
    exact suppress_down_left fs cs d l r marks valid canonical absent nonempty (eq ▸ destination)
  · have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
    simp only [Pointer.offset, Pointer.offset_append] at index
    have eq : y = Pointer.offset (Context.referencePath fs) + Pointer.offset cs +
        l.reference.size + 1 + rootRank r.reference := by omega
    exact suppress_down_right fs cs d l r marks valid canonical absent nonempty (eq ▸ destination)
  · have nonempty : Pointer.plug [f] (.node l.reference r.reference) ≠ .nil := by cases f <;> simp [Pointer.plug]
    have index := Option.some.inj ((key_at_root _ _ nonempty).symm.trans touched)
    obtain ⟨after, k, afterValid, ref, normal, suppression, trace, cost⟩ :=
      suppress_up fs cs d l r marks valid canonical absent f anc path (index.symm ▸ marked)
    exact ⟨after, k, afterValid, ref, normal, suppression, trace, by omega⟩

end RotationBST.FingerHand.Hand
