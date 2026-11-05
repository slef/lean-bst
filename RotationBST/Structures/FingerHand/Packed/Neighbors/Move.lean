module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Canonical
public import RotationBST.Structures.FingerHand.Pruning.State

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- A tree-preserving multifinger step has a physical preparation retaining
every target-state mark. Pruning its labelled skeleton gives exactly the target
hand. Physically suppressing the obsolete marks is a subsequent obligation. -/
theorem prepare_move {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t)
    (sameTree : t.tree = s.tree) :
    ∃ (after : Hand) (k : Nat), Exposure h after (t.position i) ∧ after.reference = t.tree ∧
      (∀ j, t.position j ∈ (after.labels 0).inorder) ∧
      after.labels 0 = compress (insert (t.position i) (stateMarks s)) t.tree 0 ∧
      prune (stateMarks t) (after.labels 0) = ofState t ∧
      after.count ≤ (ofState t).erase.size + 2 ∧
      after.count ≤ 2 * (fingers + 1) + 1 ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 180 + 20 * (fingers + 1) + h.potential := by
  obtain ⟨after, k, ex, canonical, trace, cost⟩ := prepare_instruction rep valid step
  have reference : after.reference = t.tree := ex.reference.trans (rep.2.1.trans sameTree.symm)
  have allFingers : ∀ j, t.position j ∈ (after.labels 0).inorder := by
    intro j
    by_cases eq : j = i
    · subst j
      exact ex.retained
    · rw [step.inactive j eq]
      exact (ex.keys 0).subset (rep.finger valid j)
  have root : rootRank t.tree ∈ (after.labels 0).inorder := by
    rw [sameTree]
    apply (ex.keys 0).subset
    rw [rep.2.2]
    have range := valid i
    exact ofState_root s (by omega)
  have projected := after.prune_labels (stateMarks t) 0 (by
    intro x _ marked
    rcases Finset.mem_insert.mp marked with rfl | marked
    · exact root
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp marked
      exact allFingers j)
  rw [reference] at projected
  rw [reference] at canonical
  have jointMarks : insert (t.position i) (stateMarks s) = insert (s.position i) (stateMarks t) := by
    rw [stateMarks_stationary s i, step_stationary_marks step sameTree, Finset.insert_comm]
  have excess : after.count ≤ (ofState t).erase.size + 2 := by
    rw [← labels_size after 0, canonical, jointMarks]
    exact compress_insert_size _ _ _ _
  have count := ex.count
  have size := rep.count
  exact ⟨after, k, ex, reference, allFingers, canonical, projected, excess, by omega, trace, cost⟩

/-- If the old finger key remains in the target skeleton, preparation already
completes the move. This includes an inactive coincident finger, the root
anchor, or a vertex still needed as an unmarked branch. -/
theorem move_retained {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t)
    (sameTree : t.tree = s.tree) (retained : s.position i ∈ (ofState t).inorder) :
    ∃ (after : Hand) (k : Nat), after.Represents t ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 180 + 20 * (fingers + 1) + h.potential := by
  obtain ⟨after, k, ex, reference, _, canonical, _, _, _, trace, cost⟩ := prepare_move rep valid step sameTree
  have jointMarks : insert (t.position i) (stateMarks s) = insert (s.position i) (stateMarks t) := by
    rw [stateMarks_stationary s i, step_stationary_marks step sameTree, Finset.insert_comm]
  have harmless := (build (stateMarks t) t.tree 0).mark_retained (stateMarks t) 0 (s.position i)
    (by rw [build_reference, build_labels]) (by rw [build_labels]; exact retained)
  simp only [build_reference, build_labels] at harmless
  rw [jointMarks, ← harmless] at canonical
  exact ⟨after, k, ⟨ex.valid, reference, canonical⟩, trace, cost⟩

end RotationBST.FingerHand.Hand
