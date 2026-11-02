module

public import RotationBST.Tango.State.Basic

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

private theorem root_sum (s : MarkedTree) (lo : Nat) :
    ((s.rootComponent lo).map fun p => auxiliaryPotential p.2).sum = auxiliaryPotential s.region := by
  cases s <;> simp [rootComponent, region, auxiliaryPotential_hole]

private theorem detached_sum_offset (s : MarkedTree) (lo : Nat) :
    ((s.detached lo).map fun p => auxiliaryPotential p.2).sum =
      ((s.detached 0).map fun p => auxiliaryPotential p.2).sum := by
  induction s generalizing lo with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp only [detached, Bool.false_eq_true, ite_false, ite_true, List.map_append, List.sum_append,
        List.map_nil, List.sum_nil, root_sum, il, ir]

theorem component_sum (s : MarkedTree) (lo : Nat) :
    ((s.components lo).map fun p => auxiliaryPotential p.2).sum = s.potential := by
  simp only [potential, components, List.map_append, List.sum_append, root_sum, detached_sum_offset]

theorem potential_decompose (s : MarkedTree) (lo : Nat) :
    s.potential = auxiliaryPotential s.region +
      ((s.detached lo).map fun p => auxiliaryPotential p.2).sum := by
  rw [← component_sum s lo]
  simp only [components, List.map_append, List.sum_append, root_sum]

/-- Every node contributes the logarithm of its active descendant count.
Marks stop this count, but never remove the potential of a detached component. -/
theorem potential_node (l r : MarkedTree) (cl cr : Bool) :
    (MarkedTree.node l r cl cr).potential = l.potential + r.potential +
      Real.logb 2 (MarkedTree.node l r cl cr).region.size := by
  rw [potential_decompose (.node l r cl cr) 0, potential_decompose l 0,
    potential_decompose r (0 + l.tree.size + 1)]
  cases cl <;> cases cr <;>
    simp only [region, detached, Bool.false_eq_true, ite_false, ite_true, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil, root_sum, auxiliaryPotential_node,
      auxiliaryPotential_hole, size]
  all_goals
    simp only [add_assoc, add_comm, add_left_comm,
      zero_add, add_zero]

theorem initial_potential (t : Tree) : (initial t).potential = 0 := by
  induction t with
  | nil => rfl
  | node l r il ir =>
    rw [initial, potential_node, il, ir]
    simp [region, size]

end RotationBST.Tango.MarkedTree
