module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.State.Nesting.Locate
public import RotationBST.Tango.State.Nesting.Partition

@[expose] public section
namespace RotationBST.Tango.State.Nesting.Results
open MarkedTree

/-- The reference marking realizes both the preferred paths and their nesting. -/
theorem canonical_state (reference : Tree) (past : List Nat) :
    (canonical reference 0 past).tree = reference ∧
      Maintains (canonical reference 0 past) reference past :=
  ⟨canonical_tree reference 0 past, canonical_maintains reference past⟩

theorem initial_state (reference : Tree) : Maintains (initial reference) reference [] :=
  initial_maintains reference

/-- Internal auxiliary rearrangement preserves the stronger maintenance invariant. -/
theorem reshape {s t : MarkedTree} {reference : Tree} {past : List Nat}
    (maintained : Maintains s reference past) (fringe : s.fringe = t.fringe) :
    Maintains t reference past := maintains_of_fringe maintained fringe

/-- The final access preserves component nesting and the preferred-path partition. -/
theorem access (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) (x : Nat) (valid : x ∈ s.region.keys 0) :
    ∃ u : MarkedTree, ∃ cost : Nat, Access s.tree u.tree x cost ∧ Maintains u reference past ∧
      (cost : ℝ) + u.potential - s.potential ≤ 3 * Real.logb 2 (height reference) + 1 :=
  maintained_access s reference past maintained x valid

/-- Forgetting auxiliary shape preserves the represented key count. -/
theorem same_size {s t : MarkedTree} (same : s.nesting = t.nesting) : s.tree.size = t.tree.size :=
  nesting_size_eq same

/-- Nesting alone determines all component key sets, in their traversal order. -/
theorem component_keys {s t : MarkedTree} (same : s.nesting = t.nesting) (lo : Nat) :
    ((s.components lo).map fun p => p.2.keys p.1) =
      ((t.components lo).map fun p => p.2.keys p.1) := nesting_components_eq s t same lo

/-- To maintain the reference partition, it suffices to maintain its nesting. -/
theorem maintenance_iff (s : MarkedTree) (reference : Tree) (past : List Nat) :
    Maintains s reference past ↔ s.nesting = (canonical reference 0 past).nesting :=
  ⟨fun h => h.2, maintains_of_nesting s reference past⟩

/-- Corresponding attached components have identical offsets and nesting. -/
theorem fringe_matching {s t : MarkedTree} (same : s.nesting = t.nesting) (lo : Nat) :
    List.Forall₂ (fun a b : Nat × MarkedTree => a.1 = b.1 ∧ a.2.nesting = b.2.nesting)
      (s.fringeAt lo) (t.fringeAt lo) := fringeAt_matching same lo

/-- Locate a reference fringe component in the actual maintained BST. -/
theorem locate (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) {p : Nat × MarkedTree}
    (member : p ∈ (canonical reference 0 past).fringeAt 0) (nonempty : p.2 ≠ .nil) :
    ∃ child : MarkedTree, ∃ fs : List Context.Frame,
      (p.1, child) ∈ s.fringeAt 0 ∧ child.nesting = p.2.nesting ∧
      fs ≠ [] ∧ Context.Boundary fs ∧ Context.plug fs child = s :=
  locate_reference_component s reference past maintained member nonempty

/-- The locating context selects the reference component's exact key offset. -/
theorem locate_at (s : MarkedTree) (reference : Tree) (past : List Nat)
    (maintained : Maintains s reference past) {p : Nat × MarkedTree}
    (member : p ∈ (canonical reference 0 past).fringeAt 0) (nonempty : p.2 ≠ .nil) :
    ∃ child : MarkedTree, ∃ fs : List Context.Frame,
      (p.1, child) ∈ s.fringeAt 0 ∧ child.nesting = p.2.nesting ∧
      fs ≠ [] ∧ Context.Boundary fs ∧ Context.plug fs child = s ∧ Context.offset fs 0 = p.1 :=
  locate_reference_component_at s reference past maintained member nonempty

end RotationBST.Tango.State.Nesting.Results

#check_bst_abstract RotationBST.Tango.State.Nesting.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.State.Definitions.Abstract,
  RotationBST.Tango.State.Canonical.Abstract, RotationBST.Tango.State.Nesting.Abstract,
  RotationBST.Tango.State.Context.Abstract,
  RotationBST.Tango.Definitions.Abstract, RotationBST.Tango.Paths.Abstract,
  RotationBST.Tango.Wilber.Abstract, RotationBST.Tango.Transition.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
