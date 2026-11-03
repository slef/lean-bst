module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.State.Initial
public import RotationBST.Algorithms.Tango.State.Bounds
public import RotationBST.Algorithms.Tango.State.Updates.Results

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
    (represented : Represents s reference past) {p : Nat × Region}
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
    s.potential = Region.auxiliaryPotential s.region + (s.fringe.map potential).sum :=
  ⟨potential_nonneg s, potential_fringe s⟩

end RotationBST.Tango.State.Results

/-- info: abstract audit passed for `RotationBST.Tango.State.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.State.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.State.Defs,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract, RotationBST.Models.Region.Defs, RotationBST.Bounds.Interleave.Wilber.Defs, RotationBST.Algorithms.Tango.State.Abstract, RotationBST.Bounds.Interleave.Transition.Defs]
