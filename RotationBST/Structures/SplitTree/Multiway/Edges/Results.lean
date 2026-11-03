module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Edges.Bounds

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Edges.Results

/-- Repair the first child of any parent: preserve balance and use at most five
binary rotations, while never increasing the merge reserve. -/
theorem first {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (t.repairFirst).1.binary (t.repairFirst).2 ∧
      (t.repairFirst).2 ≤ 5 ∧ (t.repairFirst).1.nodes ≤ t.nodes ∧
      (Balanced h (t.repairFirst).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.repairFirst).1) :=
  ⟨repairFirst_rotations t, repairFirst_cost t, repairFirst_nodes t, valid.repairFirst⟩

/-- Repair the last child with the analogous bound of four rotations. -/
theorem last {h : Nat} {t : Multiway} (valid : Balanced h t) :
    Rotations t.binary (t.repairLast).1.binary (t.repairLast).2 ∧
      (t.repairLast).2 ≤ 4 ∧ (t.repairLast).1.nodes ≤ t.nodes ∧
      (Balanced h (t.repairLast).1 ∨ ∃ k, h = k + 1 ∧ Balanced k (t.repairLast).1) :=
  ⟨repairLast_rotations t, repairLast_cost t, repairLast_nodes t, valid.repairLast⟩

/-- A merge in a larger parent consumes exactly one multiway node. -/
theorem merge_three (a b c d e : Multiway) :
    (.two (.four a b c d) e : Multiway).nodes + 1 =
        (.three (.two a b) (.two c d) e : Multiway).nodes ∧
      (.two a (.four b c d e) : Multiway).nodes + 1 =
        (.three a (.two b c) (.two d e) : Multiway).nodes :=
  ⟨merge_first_three_nodes a b c d e, merge_last_three_nodes a b c d e⟩

theorem merge_four (a b c d e f : Multiway) :
    (.three (.four a b c d) e f : Multiway).nodes + 1 =
        (.four (.two a b) (.two c d) e f : Multiway).nodes ∧
      (.three a b (.four c d e f) : Multiway).nodes + 1 =
        (.four a b (.two c d) (.two e f) : Multiway).nodes :=
  ⟨merge_first_four_nodes a b c d e f, merge_last_four_nodes a b c d e f⟩

end RotationBST.SplitTree.Multiway.Edges.Results

/-- info: abstract audit passed for `RotationBST.SplitTree.Multiway.Edges.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.SplitTree.Multiway.Edges.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs]
