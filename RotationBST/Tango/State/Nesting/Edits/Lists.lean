module

public import RotationBST.Tango.State.Nesting.Edits.Abstract
public import RotationBST.Tango.State.Nesting.Matching

@[expose] public section
namespace RotationBST.Tango.ComponentNesting

theorem group_append (a b c : List ComponentNesting) :
    group (.branch (a ++ b ++ c)) a.length b.length = .branch (a ++ [.branch b] ++ c) := by
  simp [group, List.drop_append, List.append_assoc]

theorem merge_append (a c : List ComponentNesting) (b : ComponentNesting) :
    merge (.branch (a ++ [b] ++ c)) a.length = .branch (a ++ b.fringe ++ c) := by
  simp [merge, List.drop_append, List.append_assoc]

end RotationBST.Tango.ComponentNesting

namespace RotationBST.Tango.MarkedTree

theorem nesting_branch (s : MarkedTree) (nonempty : s ≠ .nil) :
    s.nesting = .branch s.nesting.fringe := by
  cases s with
  | nil => contradiction
  | node l r cl cr => rfl

theorem nesting_fringe_length (s : MarkedTree) : s.nesting.fringe.length = s.region.size + 1 := by
  rw [nesting_fringe, List.length_map, marked_fringe_length]

end RotationBST.Tango.MarkedTree
