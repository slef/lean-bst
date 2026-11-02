module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Nesting.ExecutableReplacement

@[expose] public section
namespace RotationBST.Tango.State.Lookup.Results
open MarkedTree Context

theorem locate (s child : MarkedTree) (i : Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil) :
    ∃ fs : List Frame, locateIndex s i = some (child, fs) ∧
      fs ≠ [] ∧ Boundary fs ∧ plug fs child = s ∧
      ∀ target, (plug fs target).fringe = s.fringe.set i target :=
  Context.locateIndex_spec s child i atIndex nonempty

theorem edit (s child : MarkedTree) (i : Nat) (edit : MarkedTree → MarkedTree × Nat)
    (atIndex : s.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (rotations : Rotations child.tree (edit child).1.tree (edit child).2) :
    (editFringe s i edit).2 = (edit child).2 ∧
      (editFringe s i edit).1.fringe = s.fringe.set i (edit child).1 ∧
      (editFringe s i edit).1.nesting = .branch ((s.fringe.map nesting).set i (edit child).1.nesting) ∧
      Rotations s.tree (editFringe s i edit).1.tree (editFringe s i edit).2 ∧
      (editFringe s i edit).1.potential - s.potential = (edit child).1.potential - child.potential :=
  Context.editFringe_spec s child i edit atIndex nonempty rotations

theorem simulate (s reference child target : MarkedTree) (i : Nat) (bound : ℝ)
    (edit : MarkedTree → MarkedTree × Nat) (same : s.nesting = reference.nesting)
    (atIndex : reference.fringe[i]? = some child) (nonempty : child ≠ .nil)
    (localUpdate : ∀ actual : MarkedTree, actual.nesting = child.nesting →
      (edit actual).1.nesting = target.nesting ∧
        Rotations actual.tree (edit actual).1.tree (edit actual).2 ∧
        ((edit actual).2 : ℝ) + (edit actual).1.potential - actual.potential ≤ bound) :
    (Context.editFringe s i edit).1.nesting = .branch (reference.nesting.fringe.set i target.nesting) ∧
      Rotations s.tree (Context.editFringe s i edit).1.tree (Context.editFringe s i edit).2 ∧
      ((Context.editFringe s i edit).2 : ℝ) + (Context.editFringe s i edit).1.potential - s.potential ≤ bound :=
  MarkedTree.editFringe_simulates s reference child target i bound edit same atIndex nonempty localUpdate

end RotationBST.Tango.State.Lookup.Results

#check_bst_abstract RotationBST.Tango.State.Lookup.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Context.Abstract, RotationBST.Tango.State.Context.Lookup.Abstract,
  RotationBST.Tango.State.Nesting.Abstract, RotationBST.Arboral.Treap.Regions.Abstract,
  RotationBST.Tango.Auxiliary.Definitions.Abstract, RotationBST.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Pointer.Traces, RotationBST.Pointer.Machine.Abstract,
  RotationBST.Splay.Algorithm.Abstract, RotationBST.Splay.Potential.Abstract]
