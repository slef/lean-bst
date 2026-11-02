module

public import RotationBST.Tango.State.Cut
public import RotationBST.Tango.State.Join.Interior

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- Merge the final attached component using a maximum splay. The resulting
state removes the boundary mark, and the bound charges the full-state potential. -/
theorem join_back (s right : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.getLast? = some right) :
    ∃ l : MarkedTree, ∃ cl : Bool, ∃ cost : Nat,
      s.fringe = (MarkedTree.node l right cl true).fringe ∧
      Rotations s.tree (MarkedTree.node l right cl false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l right cl false).potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + right.region.size : Nat) + 1 := by
  obtain ⟨l, cl, result, fringe, rotations, bound⟩ := joinBack_spec s right positive attached
  refine ⟨l, cl, s.joinBack.2, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

/-- Merge the first attached component using a minimum splay. -/
theorem join_front (s left : MarkedTree) (positive : 0 < s.region.size)
    (attached : s.fringe.head? = some left) :
    ∃ r : MarkedTree, ∃ cr : Bool, ∃ cost : Nat,
      s.fringe = (MarkedTree.node left r true cr).fringe ∧
      Rotations s.tree (MarkedTree.node left r false cr).tree cost ∧
      (cost : ℝ) + (MarkedTree.node left r false cr).potential - s.potential ≤
        3 * Real.logb 2 (s.region.size + left.region.size : Nat) + 1 := by
  obtain ⟨r, cr, result, fringe, rotations, bound⟩ := joinFront_spec s left positive attached
  refine ⟨r, cr, s.joinFront.2, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

/-- Merge an interior attached component. The two boundary splays change the
stored marks and charge all rotations against the full-state potential. -/
theorem join_interior (s middle : MarkedTree) (i : Nat)
    (positive : 0 < i) (interior : i < s.region.size)
    (attached : s.fringe[i]? = some middle) :
    ∃ a c : MarkedTree, ∃ ca cc : Bool, ∃ cost : Nat,
      (if ca then 0 else a.region.size) + 1 = i ∧
      s.fringe = (MarkedTree.node a (.node middle c true cc) ca false).fringe ∧
      Rotations s.tree (MarkedTree.node a (.node middle c false cc) ca false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node a (.node middle c false cc) ca false).potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + middle.region.size : Nat) + 2 := by
  obtain ⟨a, c, ca, cc, result, rank, fringe, rotations, bound⟩ :=
    joinInterior_spec s middle i positive interior attached
  refine ⟨a, c, ca, cc, (s.joinInterior i).2, rank, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

end RotationBST.Tango.MarkedTree
