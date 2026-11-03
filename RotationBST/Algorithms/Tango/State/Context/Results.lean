module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Context.Localization

@[expose] public section
namespace RotationBST.Tango.Context.Results

/-- A local component update retains its exact rotation count and potential
change when embedded below a marked boundary of the full BST. -/
theorem embed (whole child target : MarkedTree) (member : child ∈ whole.fringe)
    (nonempty : child ≠ .nil) {cost : Nat} (rotations : Rotations child.tree target.tree cost) :
    ∃ result : MarkedTree, Rotations whole.tree result.tree cost ∧
      result.potential - whole.potential = target.potential - child.potential :=
  embed_update whole child target member nonempty rotations

/-- The nearest edge must be marked; higher ancestors may have either mark. -/
theorem potential_change (fs : List Frame) (boundary : Boundary fs) (s t : MarkedTree) :
    (plug fs t).potential - (plug fs s).potential = t.potential - s.potential :=
  boundary_potential fs boundary s t

theorem nesting_preserved (fs : List Frame) {s t : MarkedTree} (same : s.nesting = t.nesting) :
    (plug fs s).nesting = (plug fs t).nesting := plug_nesting fs same

end RotationBST.Tango.Context.Results

#check_bst_abstract RotationBST.Tango.Context.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Algorithms.Tango.State.Context.Defs, RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
