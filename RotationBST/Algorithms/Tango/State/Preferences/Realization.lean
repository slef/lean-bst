module

public import RotationBST.Algorithms.Tango.State.Preferences.Location
public import RotationBST.Algorithms.Tango.State.Preferences.Algorithm.Update
public import RotationBST.Algorithms.Tango.State.Preferences.Marks

@[expose] public section
namespace RotationBST.Tango.MarkedTree

/-- Realize one rank-based reference preference update by actual BST rotations.
The reference height bounds the cost uniformly at every intermediate marking. -/
theorem realize_preference (s reference : MarkedTree) (key : Nat) (next : Bool)
    (same : s.nesting = reference.nesting) (paths : reference.PathMarked)
    (valid : key < reference.tree.size) :
    ∃ result : MarkedTree, ∃ cost : Nat,
      result.nesting = (reference.setPreference key next).nesting ∧
      Rotations s.tree result.tree cost ∧
      (cost : ℝ) + result.potential - s.potential ≤ 14 * Real.logb 2 (height reference.tree) + 4 := by
  exact ⟨(s.updatePreference reference key next).1, (s.updatePreference reference key next).2,
    updatePreference_spec s reference key next same paths valid⟩

end RotationBST.Tango.MarkedTree
