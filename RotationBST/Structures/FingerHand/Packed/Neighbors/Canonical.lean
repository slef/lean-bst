module

public import RotationBST.Structures.FingerHand.Packed.Neighbors.Instruction
public import RotationBST.Structures.FingerHand.Packed.Updates.Marks

@[expose] public section
namespace RotationBST.FingerHand.Hand

theorem Exposure.expansion {a b : Hand} {x : Nat} (ex : Exposure a b x) (valid : a.Valid)
    (fresh : x ∉ (a.labels 0).inorder) : Expansion a b := by
  have strict : (a.labels 0).inorder.length < (b.labels 0).inorder.length := by
    have weak := (ex.keys 0).length_le
    by_contra h
    have eq := (ex.keys 0).eq_of_length (by omega)
    exact fresh (eq ▸ ex.retained)
  simp only [Representation.Bridge.inorder_length, labels_size] at strict
  have count := ex.count
  exact ⟨valid, ex.valid, ex.reference, by omega, ex.keys⟩

/-- Prepare the actual instruction destination with precisely the old marks
plus that key. If it is already retained, no physical work is performed. -/
theorem prepare_instruction {fingers : Nat} {h : Hand} {s t : Multifinger.State fingers}
    {i : Fin fingers} (rep : h.Represents s) (valid : s.Valid) (step : Multifinger.Step s i t) :
    ∃ (after : Hand) (k : Nat), Exposure h after (t.position i) ∧
      after.labels 0 = compress (insert (t.position i) (stateMarks s)) after.reference 0 ∧
      Pointer.Trace ⟨h.tree, []⟩ ⟨after.tree, []⟩ k ∧
      k + after.potential ≤ 180 + 20 * (fingers + 1) + h.potential := by
  have canonical : h.labels 0 = compress (stateMarks s) h.reference 0 := by
    rw [rep.2.1]
    exact rep.2.2
  by_cases member : t.position i ∈ (h.labels 0).inorder
  · exact ⟨h, 0, ⟨rep.1, rfl, fun _ => .refl _, by omega, member⟩,
      h.mark_retained (stateMarks s) 0 _ canonical member, .refl, by omega⟩
  · obtain ⟨after, k, ex, trace, cost⟩ := expose_instruction rep valid step
    exact ⟨after, k, ex, (ex.expansion rep.1 member).mark_added (stateMarks s) 0 _ canonical member ex.retained,
      trace, cost⟩

end RotationBST.FingerHand.Hand
