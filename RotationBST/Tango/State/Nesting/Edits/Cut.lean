module

public import RotationBST.Tango.State.Nesting.Edits.Marking
public import RotationBST.Tango.State.Nesting.Edits.Algorithm.Cut

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Every nonempty proper key interval can be split into its own component.
The resulting nesting is exactly the grouping of its consecutive fringe slots. -/
theorem cut_nesting (s : MarkedTree) (i j : Nat) (ordered : i < j)
    (valid : j ≤ s.region.size) (proper : j - i < s.region.size) :
    ∃ t : MarkedTree, ∃ cost : Nat,
      t.nesting = s.nesting.group i (j - i + 1) ∧ Rotations s.tree t.tree cost ∧
      (cost : ℝ) + t.potential - s.potential ≤ 6 * Real.logb 2 s.region.size + 2 := by
  exact ⟨(s.cutInterval i j).1, (s.cutInterval i j).2, cutInterval_spec s i j ordered valid proper⟩

end RotationBST.Tango.MarkedTree
