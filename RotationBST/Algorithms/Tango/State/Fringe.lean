module

public import RotationBST.Algorithms.Tango.State.Potential

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Geometric.Region

@[simp] theorem potential_nil : MarkedTree.nil.potential = 0 := rfl

theorem fringe_tree (s : MarkedTree) : s.fringe.map tree = s.region.fringe := by
  induction s with
  | nil => rfl
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp [fringe, region, Pointer.Lazy.Skeleton.fringe, il, ir]

theorem marked_fringe_length (s : MarkedTree) : s.fringe.length = s.region.size + 1 := by
  have h := congrArg List.length (fringe_tree s)
  simpa only [List.length_map, Pointer.Lazy.Skeleton.fringe_length] using h

theorem region_size_eq {s t : MarkedTree} (same : s.fringe = t.fringe) :
    s.region.size = t.region.size := by
  have eq : s.region.fringe = t.region.fringe := by rw [← fringe_tree, ← fringe_tree, same]
  have lengths := congrArg List.length eq
  simpa only [Pointer.Lazy.Skeleton.fringe_length, Nat.add_right_cancel_iff] using lengths

/-- The potential below the root component depends only on the marked fringe.
Consequently it is unchanged by rotations confined to that component. -/
theorem potential_fringe (s : MarkedTree) :
    s.potential = auxiliaryPotential s.region + (s.fringe.map potential).sum := by
  induction s with
  | nil => simp [region, fringe, auxiliaryPotential_hole]
  | node l r cl cr il ir =>
    rw [potential_node]
    cases cl <;> cases cr <;>
      simp only [fringe, region, Bool.false_eq_true, ite_false, ite_true, List.map_append,
        List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        auxiliaryPotential_node, auxiliaryPotential_hole, Pointer.Lazy.Skeleton.size]
    all_goals
      simp only [add_assoc, add_comm, zero_add, add_zero] at *
    all_goals linarith

theorem potential_difference {s t : MarkedTree} (same : s.fringe = t.fringe) :
    t.potential - s.potential = auxiliaryPotential t.region - auxiliaryPotential s.region := by
  rw [potential_fringe s, potential_fringe t, same]
  ring

end RotationBST.Tango.MarkedTree
