module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Context.Localization

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
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Context.Abstract, RotationBST.Tango.State.Nesting.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
