module

public import RotationBST.Tango.State.Context.Lookup.Proofs

@[expose] public section
namespace RotationBST.Tango.Context
open MarkedTree

/-- Locate a fringe occurrence by index, retaining the exact effect of replacing
it. In particular, equal subtree shapes at other positions are left alone. -/
theorem locate_fringe_index (s child : MarkedTree) (i : Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil) :
    ∃ fs : List Frame, fs ≠ [] ∧ Boundary fs ∧ plug fs child = s ∧
      ∀ target, (plug fs target).fringe = s.fringe.set i target := by
  obtain ⟨fs, _, hn, hb, hp, hr⟩ := locateIndex_spec s child i atIndex nonempty
  exact ⟨fs, hn, hb, hp, hr⟩

theorem plug_nonempty (fs : List Frame) (s : MarkedTree) (nonempty : fs ≠ []) :
    plug fs s ≠ .nil := by
  induction fs generalizing s with
  | nil => contradiction
  | cons f fs ih =>
    cases fs with
    | nil => cases f <;> simp [plug, Frame.fill]
    | cons g gs => exact ih _ (by simp)

/-- An update at a specified fringe slot changes just that nesting entry and
retains its exact local rotation count and potential change in the whole BST. -/
theorem replace_fringe (s child target : MarkedTree) (i : Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil)
    {cost : Nat} (rotations : Rotations child.tree target.tree cost) :
    ∃ result : MarkedTree,
      result.nesting = .branch ((s.fringe.map nesting).set i target.nesting) ∧
      Rotations s.tree result.tree cost ∧
      result.potential - s.potential = target.potential - child.potential := by
  obtain ⟨fs, hn, hb, hp, hr⟩ := locate_fringe_index s child i atIndex nonempty
  refine ⟨plug fs target, ?_, ?_, ?_⟩
  · have fringe := congrArg (List.map nesting) (hr target)
    rw [List.map_set, ← nesting_fringe] at fringe
    have node : (plug fs target).nesting = .branch (plug fs target).nesting.fringe := by
      have h := plug_nonempty fs target hn
      cases heq : plug fs target with
      | nil => exact False.elim (h heq)
      | node l r cl cr => rfl
    rw [node, fringe]
  · simpa only [hp] using plug_rotations fs rotations
  · simpa only [hp] using boundary_potential fs hb child target

end RotationBST.Tango.Context
