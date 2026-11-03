module

public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Marking
public import RotationBST.Algorithms.Tango.State.Nesting.Edits.Algorithm.Merge

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Every attached component can be merged into the root component. The actual
marked-state update implements exactly the corresponding nesting splice. -/
theorem merge_nesting (s child : MarkedTree) (i : Nat) (positive : 0 < s.region.size)
    (valid : i ≤ s.region.size) (attached : s.fringe[i]? = some child) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = s.nesting.merge i ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤
        8 * Real.logb 2 (s.region.size + child.region.size : Nat) + 2 := by
  exact ⟨(s.mergeAt i).1, (s.mergeAt i).2, mergeAt_spec s child i positive valid attached⟩

end RotationBST.Tango.MarkedTree
