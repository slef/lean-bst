module

public import RotationBST.Tango.State.Nesting.Proofs
public import Mathlib.Data.List.Forall2

@[expose] public section
namespace RotationBST.Tango

theorem ComponentNesting.fringe_span (n : ComponentNesting) :
    (n.fringe.map ComponentNesting.span).sum = n.span := by
  cases n <;> simp [ComponentNesting.fringe, ComponentNesting.span]

namespace MarkedTree

/-- The nesting signature retains exact subtree sizes, despite forgetting each
auxiliary component's binary shape. -/
theorem nesting_span (s : MarkedTree) : s.nesting.span = s.tree.size + 1 := by
  induction s with
  | nil => simp [nesting, ComponentNesting.span, tree, Tree.size]
  | node l r cl cr il ir =>
    cases cl <;> cases cr <;>
      simp only [nesting, ComponentNesting.span, Bool.false_eq_true, ite_false, ite_true,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        ComponentNesting.fringe_span, il, ir, tree, Tree.size] <;> omega

theorem nesting_size_eq {s t : MarkedTree} (same : s.nesting = t.nesting) : s.tree.size = t.tree.size := by
  have sizes := congrArg ComponentNesting.span same
  simpa only [nesting_span, Nat.add_right_cancel_iff] using sizes

theorem nesting_region_size_eq {s t : MarkedTree} (same : s.nesting = t.nesting) :
    s.region.size = t.region.size := by
  have lengths := congrArg (fun n : ComponentNesting => n.fringe.length) same
  rw [nesting_fringe, nesting_fringe, List.length_map, List.length_map,
    marked_fringe_length, marked_fringe_length] at lengths
  omega

/-- Corresponding fringe slots have the same recursively nested components. -/
theorem nesting_fringe_matching {s t : MarkedTree} (same : s.nesting = t.nesting) :
    List.Forall₂ (fun a b : MarkedTree => a.nesting = b.nesting) s.fringe t.fringe := by
  have h := congrArg ComponentNesting.fringe same
  rw [nesting_fringe, nesting_fringe] at h
  have eq : List.Forall₂ Eq (s.fringe.map nesting) (t.fringe.map nesting) := by
    rw [h]
    exact List.forall₂_refl _
  simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using eq

end MarkedTree
end RotationBST.Tango
