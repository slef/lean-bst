module

public import RotationBST.Algorithms.Tango.State.Context.Replacement

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- Editing a selected component is executable and changes exactly its fringe
slot. The local rotation count and potential difference transfer unchanged. -/
theorem editFringe_spec (s child : MarkedTree) (i : Nat) (edit : MarkedTree → MarkedTree × Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (rotations : Rotations child.tree (edit child).1.tree (edit child).2) :
    (editFringe s i edit).2 = (edit child).2 ∧
      (editFringe s i edit).1.fringe = s.fringe.set i (edit child).1 ∧
      (editFringe s i edit).1.nesting = .branch ((s.fringe.map nesting).set i (edit child).1.nesting) ∧
      Rotations s.tree (editFringe s i edit).1.tree (editFringe s i edit).2 ∧
      (editFringe s i edit).1.potential - s.potential = (edit child).1.potential - child.potential := by
  obtain ⟨fs, found, hn, hb, hp, hr⟩ := locateIndex_spec s child i atIndex nonempty
  simp only [editFringe, found]
  refine ⟨True.intro, hr _, ?_, ?_, ?_⟩
  · have fringe := congrArg (List.map nesting) (hr (edit child).1)
    rw [List.map_set, ← nesting_fringe] at fringe
    have node : (plug fs (edit child).1).nesting = .branch (plug fs (edit child).1).nesting.fringe := by
      have h := plug_nonempty fs (edit child).1 hn
      cases heq : plug fs (edit child).1 with
      | nil => exact False.elim (h heq)
      | node l r cl cr => rfl
    rw [node, fringe]
  · simpa only [hp] using plug_rotations fs rotations
  · simpa only [hp] using boundary_potential fs hb child (edit child).1

end RotationBST.Tango.Context
