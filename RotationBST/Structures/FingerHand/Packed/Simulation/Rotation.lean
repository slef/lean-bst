module

public import RotationBST.Structures.FingerHand.Packed.Simulation.RotationPrepared
public import RotationBST.Structures.FingerHand.Packed.Simulation.RotationFinish
public import RotationBST.Structures.FingerHand.Packed.Neighbors.Canonical
public import RotationBST.Structures.FingerHand.Pruning.RotationState

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Complete right rotation at an actual finger: expose its parent, rotate the
prepared hand, and remove the temporary parent mark if it becomes obsolete. -/
theorem simulate_rotate_right {fingers : Nat} {h : Hand} {s : Multifinger.State fingers} (i : Fin fingers)
    (rep : h.Represents s) (valid : s.Valid) (a b c : Tree) (anc : List Pointer.Frame)
    (reference : s.tree = Pointer.plug anc (.node (.node a b) c))
    (finger : s.position i = Pointer.offset anc + a.size) :
    ∃ (after : Hand) (k : Nat),
      after.Represents ⟨Pointer.plug anc (.node a (.node b c)), s.position⟩ ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 344 + 60 * (fingers + 1) + h.potential := by
  let p := Pointer.offset anc + (Tree.node a b).size
  have up : Multifinger.Step s i
      ⟨Pointer.plug anc (.node (.node a b) c), Function.update s.position i p⟩ :=
    .execute (a := ⟨.node a b, .left c :: anc⟩) (b := ⟨.node (.node a b) c, anc⟩)
      reference.symm (by simp only [Pointer.Config.key?, Pointer.offset, finger]) .upLeft rfl
  obtain ⟨prepared, k, ex, canonical, preparation, preparationCost⟩ := prepare_instruction rep valid up
  simp only [Function.update_self] at canonical
  have preparedReference := ex.reference.trans (rep.2.1.trans reference)
  have child : Pointer.offset anc + a.size ∈ insert p (stateMarks s) := by
    rw [← finger]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  obtain ⟨rotated, m, rotatedValid, rotatedReference, normal, count, _, rotation, rotationCost⟩ :=
    rotate_right_prepared prepared (insert p (stateMarks s)) a b c anc ex.valid preparedReference canonical
      child (Finset.mem_insert_self _ _)
  have joint : insert p (stateMarks s) =
      insert p (stateMarks (⟨Pointer.plug anc (.node a (.node b c)), s.position⟩ : Multifinger.State fingers)) := by
    simpa only [stateMarks, reference] using rotation_marks_right s.position i a b c anc finger
  rw [joint] at normal
  obtain ⟨after, n, target, cleanup, cleanupCost⟩ :=
    finish_rotation rotated ⟨Pointer.plug anc (.node a (.node b c)), s.position⟩ i p
      ⟨.node b c, .right a :: anc⟩ ⟨.node a (.node b c), anc⟩ rotatedValid rotatedReference normal
      rotatedReference.symm rotatedReference.symm
      (by simp only [Pointer.Config.key?, Pointer.offset, p, Tree.size, Nat.add_assoc])
      (by simp only [Pointer.Config.key?, finger]) .upRight
  have originalCount := rep.count
  have exposedCount := ex.count
  rw [count] at cleanupCost
  exact ⟨after, k + m + n, target, (preparation.append rotation).append cleanup, by omega⟩

/-- Symmetric complete left rotation, including changes to the root anchor. -/
theorem simulate_rotate_left {fingers : Nat} {h : Hand} {s : Multifinger.State fingers} (i : Fin fingers)
    (rep : h.Represents s) (valid : s.Valid) (a b c : Tree) (anc : List Pointer.Frame)
    (reference : s.tree = Pointer.plug anc (.node a (.node b c)))
    (finger : s.position i = Pointer.offset anc + a.size + 1 + b.size) :
    ∃ (after : Hand) (k : Nat),
      after.Represents ⟨Pointer.plug anc (.node (.node a b) c), s.position⟩ ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 344 + 60 * (fingers + 1) + h.potential := by
  let p := Pointer.offset anc + a.size
  have up : Multifinger.Step s i
      ⟨Pointer.plug anc (.node a (.node b c)), Function.update s.position i p⟩ :=
    .execute (a := ⟨.node b c, .right a :: anc⟩) (b := ⟨.node a (.node b c), anc⟩)
      reference.symm (by simp only [Pointer.Config.key?, Pointer.offset, finger]) .upRight rfl
  obtain ⟨prepared, k, ex, canonical, preparation, preparationCost⟩ := prepare_instruction rep valid up
  simp only [Function.update_self] at canonical
  have preparedReference := ex.reference.trans (rep.2.1.trans reference)
  have child : Pointer.offset anc + a.size + 1 + b.size ∈ insert p (stateMarks s) := by
    rw [← finger]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  obtain ⟨rotated, m, rotatedValid, rotatedReference, normal, count, _, rotation, rotationCost⟩ :=
    rotate_left_prepared prepared (insert p (stateMarks s)) a b c anc ex.valid preparedReference canonical
      child (Finset.mem_insert_self _ _)
  have joint : insert p (stateMarks s) =
      insert p (stateMarks (⟨Pointer.plug anc (.node (.node a b) c), s.position⟩ : Multifinger.State fingers)) := by
    simpa only [stateMarks, reference] using rotation_marks_left s.position i a b c anc finger
  rw [joint] at normal
  obtain ⟨after, n, target, cleanup, cleanupCost⟩ :=
    finish_rotation rotated ⟨Pointer.plug anc (.node (.node a b) c), s.position⟩ i p
      ⟨.node a b, .left c :: anc⟩ ⟨.node (.node a b) c, anc⟩ rotatedValid rotatedReference normal
      rotatedReference.symm rotatedReference.symm rfl
      (by simp only [Pointer.Config.key?, finger, Tree.size]; congr 1; omega) .upLeft
  have originalCount := rep.count
  have exposedCount := ex.count
  rw [count] at cleanupCost
  exact ⟨after, k + m + n, target, (preparation.append rotation).append cleanup, by omega⟩

end RotationBST.FingerHand.Hand
