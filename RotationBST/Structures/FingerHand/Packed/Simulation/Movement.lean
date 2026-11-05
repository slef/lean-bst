module

public import RotationBST.Structures.FingerHand.Packed.Simulation.Cleanup
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Move

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Every tree-preserving multifinger instruction is implemented by a single
pointer trace between valid canonical packed hands. Preparation and any needed
cleanup share their intermediate physical tree and potential. -/
theorem simulate_move {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t)
    (sameTree : t.tree = s.tree) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 324 + 40 * (fingers + 1) + h.potential := by
  by_cases retained : s.position i ∈ (ofState t).inorder
  · obtain ⟨after, k, target, trace, cost⟩ := move_retained rep valid step sameTree retained
    exact ⟨after, k, target, trace, by omega⟩
  · obtain ⟨prepared, k, ex, reference, _, canonical, _, _, count, preparation, preparationCost⟩ :=
      prepare_move rep valid step sameTree
    have oldMember := (ex.keys 0).subset (rep.finger valid i)
    have source : prepared.reference = s.tree := ex.reference.trans rep.2.1
    have jointMarks : insert (t.position i) (stateMarks s) = insert (s.position i) (stateMarks t) := by
      rw [stateMarks_stationary s i, step_stationary_marks step sameTree, Finset.insert_comm]
    have normal : prepared.labels 0 = compress (insert (s.position i) (stateMarks t)) prepared.reference 0 := by
      rw [reference, ← jointMarks]
      exact canonical
    have absent : s.position i ∉ (compress (stateMarks t) prepared.reference 0).inorder := by
      rw [reference]
      exact retained
    have marked : t.position i ∈ stateMarks t :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    cases step with
    | @execute a b x tree key instruction touched =>
      obtain ⟨after, m, afterValid, ref, afterNormal, _, cleanup, cleanupCost⟩ :=
        cleanup_obsolete prepared _ a b _ x ex.valid (tree.trans source.symm) key touched instruction
          oldMember (by simpa only [Function.update_self] using ex.retained)
          (by simpa only [Function.update_self] using marked) normal absent
      have finalReference := ref.trans reference
      refine ⟨after, k + m, ⟨afterValid, finalReference, ?_⟩, preparation.append cleanup, ?_⟩
      · rw [finalReference] at afterNormal
        exact afterNormal
      · omega

end RotationBST.FingerHand.Hand
