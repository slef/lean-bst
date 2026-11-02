module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Initial
public import RotationBST.Tango.State.Bounds
public import RotationBST.Tango.State.Updates.Abstract

@[expose] public section
namespace RotationBST.Tango.State.Results
open MarkedTree

/-- Marking every reference edge gives the initial preferred-path partition
and zero global potential, without changing the underlying BST. -/
theorem initial_state (reference : Tree) :
    (initial reference).tree = reference ∧ Represents (initial reference) reference [] ∧
      (initial reference).potential = 0 :=
  ⟨initial_tree reference, initial_represents reference, initial_potential reference⟩

/-- Every stored component is nonempty and fits within the reference height. -/
theorem component_bounds {s : MarkedTree} {reference : Tree} {past : List Nat}
    (represented : Represents s reference past) {p : Nat × Arboral.Region}
    (member : p ∈ s.components 0) : 0 < p.2.size ∧ p.2.size ≤ height reference :=
  ⟨components_nonempty s 0 p member, component_size represented member⟩

/-- Splaying in the root component preserves the preferred-path representation.
This bound uses the potential of the entire marked BST. -/
theorem access (s : MarkedTree) (reference : Tree) (past : List Nat)
    (represented : Represents s reference past) (x : Nat) (valid : x ∈ s.region.keys 0) :
    ∃ u : MarkedTree, ∃ cost : Nat, Access s.tree u.tree x cost ∧ Represents u reference past ∧
      (cost : ℝ) + u.potential - s.potential ≤ 3 * Real.logb 2 (height reference) + 1 :=
  root_access_bound s reference past represented x valid

/-- The complete potential is nonnegative; all detached components are included. -/
theorem accounting (s : MarkedTree) : 0 ≤ s.potential ∧
    s.potential = Arboral.Region.auxiliaryPotential s.region + (s.fringe.map potential).sum :=
  ⟨potential_nonneg s, potential_fringe s⟩

end RotationBST.Tango.State.Results

#check_bst_abstract RotationBST.Tango.State.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.Definitions.Abstract, RotationBST.Tango.Paths.Abstract,
  RotationBST.Tango.Wilber.Abstract, RotationBST.Tango.Transition.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
