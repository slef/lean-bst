module

public import RotationBST.Tango.State.Access
public import RotationBST.Tango.State.Cut.Interior
public import RotationBST.Tango.State.Marking

@[expose] public section
namespace RotationBST.Tango.MarkedTree
open Arboral.Region Pointer.Lazy.Skeleton

/-- Expose a boundary by its active rank, transporting all component marks. -/
theorem expose_rank (s : MarkedTree) (k : Nat) (valid : k < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl cr : Bool, ∃ cost : Nat,
      (if cl then 0 else l.region.size) = k ∧
      s.fringe = (MarkedTree.node l r cl cr).fringe ∧
      Rotations s.tree (.node l.tree r.tree) cost ∧
      (cost : ℝ) + (MarkedTree.node l r cl cr).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨l, r, cl, cr, _, rank, fringe, rotations, bound⟩ := splayRoot_expose s k valid
  exact ⟨l, r, cl, cr, (s.splayRoot k).2, rank, fringe, rotations, bound⟩

/-- Cut a nonempty proper prefix of the root component. The returned state
stores the new boundary mark; its complete potential satisfies the split bound. -/
theorem cut_prefix (s : MarkedTree) (j : Nat) (positive : 0 < j) (valid : j < s.region.size) :
    ∃ l r : MarkedTree, ∃ cr : Bool, ∃ cost : Nat,
      l.region.size = j ∧ s.fringe = (MarkedTree.node l r false cr).fringe ∧
      Rotations s.tree (MarkedTree.node l r true cr).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l r true cr).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨l, r, cr, result, rank, fringe, rotations, bound⟩ := cutPrefix_spec s j positive valid
  refine ⟨l, r, cr, (s.cutPrefix j).2, rank, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

/-- Cut a nonempty proper suffix of the root component. -/
theorem cut_suffix (s : MarkedTree) (i : Nat) (positive : 0 < i) (valid : i < s.region.size) :
    ∃ l r : MarkedTree, ∃ cl : Bool, ∃ cost : Nat,
      (if cl then 0 else l.region.size) + 1 = i ∧
      r.region.size = s.region.size - i ∧
      s.fringe = (MarkedTree.node l r cl false).fringe ∧
      Rotations s.tree (MarkedTree.node l r cl true).tree cost ∧
      (cost : ℝ) + (MarkedTree.node l r cl true).potential - s.potential ≤
        3 * Real.logb 2 s.region.size + 1 := by
  obtain ⟨l, r, cl, result, rank, size, fringe, rotations, bound⟩ := cutSuffix_spec s i positive valid
  refine ⟨l, r, cl, (s.cutSuffix i).2, rank, size, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

/-- Cut an interior interval of the root component and store the new mark.
Both boundary splays and the potential of every lower component are included. -/
theorem cut_interior (s : MarkedTree) (i j : Nat)
    (positive : 0 < i) (ordered : i < j) (interior : j < s.region.size) :
    ∃ a middle c : MarkedTree, ∃ ca cc : Bool, ∃ cost : Nat,
      (if ca then 0 else a.region.size) + 1 = i ∧ middle.region.size = j - i ∧
      s.fringe = (MarkedTree.node a (.node middle c false cc) ca false).fringe ∧
      Rotations s.tree (MarkedTree.node a (.node middle c true cc) ca false).tree cost ∧
      (cost : ℝ) + (MarkedTree.node a (.node middle c true cc) ca false).potential - s.potential ≤
        6 * Real.logb 2 s.region.size + 2 := by
  obtain ⟨a, middle, c, ca, cc, result, rank, size, fringe, rotations, bound⟩ :=
    cutInterior_spec s i j positive ordered interior
  refine ⟨a, middle, c, ca, cc, (s.cutInterior i j).2, rank, size, fringe, ?_, ?_⟩
  · simpa only [result] using rotations
  · simpa only [result] using bound

end RotationBST.Tango.MarkedTree
