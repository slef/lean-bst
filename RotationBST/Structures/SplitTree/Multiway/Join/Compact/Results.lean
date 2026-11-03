module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Capacity

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Join.Compact.Results

/-- Root absorption preserves all join guarantees, including exact rotation
cost and balance, while avoiding an unnecessary extra level. -/
theorem join {hl hr : Nat} {l r : Multiway} (left : Balanced hl l) (right : Balanced hr r) :
    let result := compact hl hr l r
    Rotations (.node l.binary r.binary) result.tree.binary result.cost ∧
      Balanced result.height result.tree ∧ result.tree.size = l.size + 1 + r.size ∧
      result.cost ≤ 3 * (hl - hr + (hr - hl)) ∧
      max hl hr ≤ result.height ∧ result.height ≤ max hl hr + 1 :=
  ⟨compact_rotations _ _ _ _, (compact_balance left right).1, compact_size _ _ _ _,
    compact_cost _ _ _ _, (compact_balance left right).2⟩

/-- Two minimal roots at equal heights merge without a rotation or height increase. -/
theorem absorb (h : Nat) (a b c d : Multiway) :
    compact h h (.two a b) (.two c d) = ⟨.four a b c d, h, 0⟩ := by
  simp [compact]

/-- A height increase always leaves a minimal root. -/
theorem growth (hl hr : Nat) (l r : Multiway)
    (increased : max hl hr < (compact hl hr l r).height) :
    rootKeys (compact hl hr l r).tree = 1 := compact_growth hl hr l r increased

end RotationBST.SplitTree.Multiway.Join.Compact.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Join.Compact.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Join.Compact.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs]
