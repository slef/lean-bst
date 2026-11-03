module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Proofs
public import RotationBST.Structures.SplitTree.Multiway.Partition.Allocation

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded

theorem fromRoot_nodes (h : Nat) (t : Multiway) :
    intervalNodes (some (fromRoot h t).1) ≤ t.nodes + 2 := by
  have bound := Multiway.Partition.children_nodes h t
  simp only [intervalNodes, fromRoot]
  omega

theorem rebalance_nodes (state : State) :
    intervalNodes (some (rebalance state).1) ≤
      (Fragment.shared state).nodes + (rebalance state).2 + 2 := by
  by_cases ready : state.left.height ≤ state.right.height + 1 ∧ state.right.height ≤ state.left.height + 1
  · simp only [rebalance, ready, and_self, ite_true, intervalNodes, Fragment.nodes]
    omega
  · have allocated := Multiway.Join.compact_allocation state.left.height state.right.height state.left.tree state.right.tree
    have root := fromRoot_nodes
      (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).height
      (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).tree
    simp only [rebalance, ready, ite_false, Fragment.nodes]
    omega

/-- Node allocation depends on the height difference, not on the full heights
traversed by endpoint conversions. -/
theorem rebalance_nodes_gap (state : State) :
    intervalNodes (some (rebalance state).1) ≤ (Fragment.shared state).nodes +
      3 * (state.left.height - state.right.height + (state.right.height - state.left.height)) + 2 := by
  by_cases ready : state.left.height ≤ state.right.height + 1 ∧ state.right.height ≤ state.left.height + 1
  · simp only [rebalance, ready, and_self, ite_true, intervalNodes, Fragment.nodes]
    omega
  · have allocated := Multiway.Join.compact_allocation state.left.height state.right.height state.left.tree state.right.tree
    have cost := Multiway.Join.compact_cost state.left.height state.right.height state.left.tree state.right.tree
    have root := fromRoot_nodes
      (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).height
      (Multiway.Join.compact state.left.height state.right.height state.left.tree state.right.tree).tree
    simp only [rebalance, ready, ite_false, Fragment.nodes]
    omega

theorem normalize_minimum_nodes (p : Multiway.Partition.Piece) :
    intervalNodes (normalize (.minimum p)).1 ≤ p.tree.nodes + 2 := by
  have bound := fromRoot_nodes p.height p.tree
  simp only [normalize]
  split
  · simp only [intervalNodes]; omega
  · exact bound

theorem normalize_maximum_nodes (p : Multiway.Partition.Piece) :
    intervalNodes (normalize (.maximum p)).1 ≤ p.tree.nodes + 2 := by
  have bound := fromRoot_nodes p.height p.tree
  simp only [normalize]
  split
  · simp only [intervalNodes]; omega
  · exact bound

/-- Restoring the shared representation allocates at most its paid rotation
count plus two nodes; no uncharged reserve proportional to tree size appears. -/
theorem normalize_nodes (fragment : Fragment) :
    intervalNodes (normalize fragment).1 ≤ fragment.nodes + (normalize fragment).2 + 2 := by
  cases fragment with
  | minimum p =>
    have bound := fromRoot_nodes p.height p.tree
    simp only [normalize, Fragment.nodes]
    split
    · simp only [intervalNodes]; omega
    · exact Nat.le_trans bound (by omega)
  | maximum p =>
    have bound := fromRoot_nodes p.height p.tree
    simp only [normalize, Fragment.nodes]
    split
    · simp only [intervalNodes]; omega
    · exact Nat.le_trans bound (by omega)
  | shared state => exact rebalance_nodes state

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded
