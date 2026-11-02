module

public import RotationBST.Arboral.View.Rotations
public import RotationBST.Arboral.Treap.Execution
public import RotationBST.Geometry.AbstractBridge

@[expose] public section
namespace RotationBST.Arboral

/-- Conventional pointer executions also admit bounded geometric solutions. -/
theorem pointer_to_offline {s t : Tree} {xs : List Nat} {cost : Nat}
    (h : Pointer.Execution s xs t cost) :
    ∃ E : Offline s.size xs, E.points.card ≤ 6 * cost := by
  obtain ⟨u, rotations, pending, hr, _, bound⟩ := Pointer.execution_to_rotations h
  obtain ⟨E, he⟩ := rotations_to_offline hr
  exact ⟨E, by omega⟩

/-- Prescribing the initial shape adds only a linear reset cost in the simple
rotation model. No final shape is prescribed. -/
theorem offline_from_initial (s : Tree) (xs : List Nat) (E : Offline s.size xs) :
    ∃ t rotations, RotationBST.Execution s xs t rotations ∧
      xs.length + rotations ≤ 2 * s.size + 99 * E.points.card := by
  cases xs with
  | nil => exact ⟨s, 0, .nil, by simp⟩
  | cons x xs =>
    obtain ⟨v, u, t, rotations, pending, hv, execution, _, bound⟩ := offline_to_rotations E
    obtain ⟨reset, hreset, resets⟩ := reset_linear s v hv.symm
    cases execution with
    | cons access tail =>
      refine ⟨u, _, .cons ⟨resets.append access.1, access.2⟩ tail, ?_⟩
      simp only [List.length_cons] at *
      omega

end RotationBST.Arboral
