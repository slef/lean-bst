module

public import RotationBST.Algorithms.Tango.State.Potential

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Pointer.Lazy.Skeleton

/-- Marking an edge splits its component and cannot increase global potential. -/
theorem mark_left (l r : MarkedTree) (cr : Bool) :
    (MarkedTree.node l r true cr).potential ≤ (MarkedTree.node l r false cr).potential := by
  rw [potential_node, potential_node]
  have sizes : (MarkedTree.node l r true cr).region.size ≤ (MarkedTree.node l r false cr).region.size := by
    cases cr <;> simp [region, size]
  linarith [Splay.Updates.log_nat_mono sizes]

theorem mark_right (l r : MarkedTree) (cl : Bool) :
    (MarkedTree.node l r cl true).potential ≤ (MarkedTree.node l r cl false).potential := by
  rw [potential_node, potential_node]
  have sizes : (MarkedTree.node l r cl true).region.size ≤ (MarkedTree.node l r cl false).region.size := by
    cases cl <;> simp [region, size]
  linarith [Splay.Updates.log_nat_mono sizes]

/-- Removing a root-edge mark increases potential by at most the logarithm of
the merged root component size. This change of marks performs no rotation. -/
theorem unmark_left (l r : MarkedTree) (cr : Bool) :
    (MarkedTree.node l r false cr).potential - (MarkedTree.node l r true cr).potential ≤
      Real.logb 2 (MarkedTree.node l r false cr).region.size := by
  rw [potential_node, potential_node]
  linarith [Bounds.logb_nat_nonneg (MarkedTree.node l r true cr).region.size]

theorem unmark_right (l r : MarkedTree) (cl : Bool) :
    (MarkedTree.node l r cl false).potential - (MarkedTree.node l r cl true).potential ≤
      Real.logb 2 (MarkedTree.node l r cl false).region.size := by
  rw [potential_node, potential_node]
  linarith [Bounds.logb_nat_nonneg (MarkedTree.node l r cl true).region.size]

/-- At a marked boundary, all local potential changes transfer exactly into
the whole BST, even when the auxiliary component's size changes. -/
theorem replace_marked_left (l u r : MarkedTree) (cr : Bool) :
    (MarkedTree.node u r true cr).potential - (MarkedTree.node l r true cr).potential =
      u.potential - l.potential := by
  rw [potential_node, potential_node]
  cases cr <;> simp only [region, ite_true, Bool.false_eq_true, ite_false, size] <;> ring

theorem replace_marked_right (l r u : MarkedTree) (cl : Bool) :
    (MarkedTree.node l u cl true).potential - (MarkedTree.node l r cl true).potential =
      u.potential - r.potential := by
  rw [potential_node, potential_node]
  cases cl <;> simp only [region, ite_true, Bool.false_eq_true, ite_false, size] <;> ring

/-- Shrinking a child's active region can only lower the contribution of its
parent. This also covers a marked child, whose active size is ignored. -/
theorem replace_right_le (l r u : MarkedTree) (cl cr : Bool)
    (smaller : u.region.size ≤ r.region.size) :
    (MarkedTree.node l u cl cr).potential - (MarkedTree.node l r cl cr).potential ≤
      u.potential - r.potential := by
  rw [potential_node, potential_node]
  have sizes : (MarkedTree.node l u cl cr).region.size ≤ (MarkedTree.node l r cl cr).region.size := by
    cases cl <;> cases cr <;> simp [region, size] <;> omega
  linarith [Splay.Updates.log_nat_mono sizes]

end RotationBST.Tango.MarkedTree
