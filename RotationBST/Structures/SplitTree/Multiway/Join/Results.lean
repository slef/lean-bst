module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Join.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Join.Results

/-- Join across one separator, paying at most three rotations per level of
height difference. The output is balanced and may grow by one level. -/
theorem join {hl hr : Nat} {l r : Multiway} (left : Balanced hl l) (right : Balanced hr r) :
    let result := run hl hr l r
    Rotations (.node l.binary r.binary) result.tree.binary result.cost ∧
      Balanced result.height result.tree ∧ result.tree.size = l.size + 1 + r.size ∧
      result.cost ≤ 3 * (hl - hr + (hr - hl)) ∧
      max hl hr ≤ result.height ∧ result.height ≤ max hl hr + 1 :=
  ⟨run_rotations _ _ _ _, (run_balance left right).1, run_size _ _ _ _,
    run_cost _ _ _ _, (run_balance left right).2⟩

end RotationBST.Geometric.Split.Multiway.Join.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Join.Results`: 1 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Join.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs]
