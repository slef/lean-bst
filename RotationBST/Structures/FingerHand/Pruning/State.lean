module

public import RotationBST.Structures.FingerHand.Pruning.Changes
public import RotationBST.Structures.FingerHand.State
public import RotationBST.Models.Multifinger.Proofs

@[expose] public section
namespace RotationBST.FingerHand

theorem stateMarks_stationary {k : Nat} (s : Multifinger.State k) (i : Fin k) :
    stateMarks s = insert (s.position i) (stationaryMarks s i) := by
  unfold stateMarks stationaryMarks
  rw [Finset.insert_comm, ← Finset.image_insert, Finset.insert_erase (Finset.mem_univ i)]

theorem stateMarks_update {k : Nat} (s : Multifinger.State k) (i : Fin k) (x : Nat) :
    stateMarks ⟨s.tree, Function.update s.position i x⟩ = insert x (stationaryMarks s i) := by
  have other : (Finset.univ.erase i).image (Function.update s.position i x) =
      (Finset.univ.erase i).image s.position := by
    apply Finset.image_congr
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  have all : Finset.univ.image (Function.update s.position i x) =
      insert x ((Finset.univ.erase i).image s.position) := by
    calc
      _ = (insert i (Finset.univ.erase i)).image (Function.update s.position i x) := by
        rw [Finset.insert_erase (Finset.mem_univ i)]
      _ = _ := by rw [Finset.image_insert, Function.update_self, other]
  simp only [stateMarks, all, stationaryMarks, Finset.insert_comm]

/-- For a legal instruction that leaves the reference tree unchanged, only the
selected finger's mark changes. Inactive coincident fingers and the root anchor
are retained explicitly. -/
theorem step_stationary_marks {k : Nat} {s t : Multifinger.State k} {i : Fin k}
    (step : Multifinger.Step s i t) (same : t.tree = s.tree) :
    stateMarks t = insert (t.position i) (stationaryMarks s i) := by
  cases step with
  | execute tree key instruction touched =>
    simp only [Function.update_self]
    dsimp only at same
    rw [same]
    exact stateMarks_update s i _

theorem stationary_root {k : Nat} (s : Multifinger.State k) (i : Fin k) :
    rootRank s.tree ∈ stationaryMarks s i := Finset.mem_insert_self _ _

theorem stationary_other {k : Nat} (s : Multifinger.State k) (i j : Fin k) (other : j ≠ i) :
    s.position j ∈ stationaryMarks s i :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨other, Finset.mem_univ _⟩, rfl⟩)

/-- Before and after changing one finger, both exact skeletons are obtained by
pruning one common skeleton. Each has at most two fewer vertices than that
common skeleton. This is a structural bound, not a pointer implementation. -/
theorem update_common_skeleton {k : Nat} (s : Multifinger.State k) (i : Fin k) (x : Nat) :
    let t : Multifinger.State k := ⟨s.tree, Function.update s.position i x⟩
    let joint := compress (insert x (stateMarks s)) s.tree 0
    prune (stateMarks s) joint = ofState s ∧
      prune (stateMarks t) joint = ofState t ∧
      joint.erase.size ≤ (ofState s).erase.size + 2 ∧
      joint.erase.size ≤ (ofState t).erase.size + 2 := by
  dsimp only
  have jointMarks : insert x (stateMarks s) =
      insert (s.position i) (stateMarks ⟨s.tree, Function.update s.position i x⟩) := by
    rw [stateMarks_update, stateMarks_stationary s i, Finset.insert_comm]
  refine ⟨prune_compress (Finset.subset_insert _ _) _ _, ?_, compress_insert_size _ _ _ _, ?_⟩
  · rw [jointMarks]
    exact prune_compress (Finset.subset_insert _ _) _ _
  · rw [jointMarks]
    exact compress_insert_size _ _ _ _

end RotationBST.FingerHand
