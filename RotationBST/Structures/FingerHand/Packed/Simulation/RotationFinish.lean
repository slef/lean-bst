module

public import RotationBST.Structures.FingerHand.Packed.Simulation.Cleanup

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Drop a temporary pivot mark after a rotation. If it remains a marked key
or required branch, the hand is already canonical. Otherwise the retained
adjacent finger supplies the verified cleanup instruction. -/
theorem finish_rotation {fingers : Nat} (h : Hand) (t : Multifinger.State fingers) (i : Fin fingers)
    (p : Nat) (a b : Pointer.Config) (valid : h.Valid) (reference : h.reference = t.tree)
    (canonical : h.labels 0 = compress (insert p (stateMarks t)) h.reference 0)
    (treeA : a.tree = h.reference) (treeB : b.tree = h.reference)
    (key : a.key? = some p) (touched : b.key? = some (t.position i))
    (adjacent : Pointer.Step a b) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 134 + 10 * h.count + h.potential := by
  by_cases retained : p ∈ (compress (stateMarks t) h.reference 0).inorder
  · have harmless := (build (stateMarks t) h.reference 0).mark_retained (stateMarks t) 0 p
      (by rw [build_reference, build_labels]) (by rw [build_labels]; exact retained)
    simp only [build_reference, build_labels] at harmless
    rw [← harmless, reference] at canonical
    exact ⟨h, 0, ⟨valid, reference, canonical⟩, .refl, by omega⟩
  · have marked : t.position i ∈ stateMarks t :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have oldMember := canonical_cursor_member h _ canonical a p treeA key (Finset.mem_insert_self _ _)
    have destination := canonical_cursor_member h _ canonical b _ treeB touched (Finset.mem_insert_of_mem marked)
    obtain ⟨after, k, afterValid, ref, normal, _, trace, cost⟩ :=
      cleanup_obsolete h _ a b p _ valid treeA key touched adjacent oldMember destination marked canonical retained
    have finalReference := ref.trans reference
    rw [finalReference] at normal
    exact ⟨after, k, ⟨afterValid, finalReference, normal⟩, trace, cost⟩

end RotationBST.FingerHand.Hand
