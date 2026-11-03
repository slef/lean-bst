module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Multiway.Context.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Context.Results

/-- A computed edit retains exactly its local rotations and reserve decrease at
any depth. In particular, cascading repairs have no extra depth factor here. -/
theorem local_edit (fs : List Frame) (s : Multiway) (operation : Multiway → Multiway × Nat)
    (steps : Rotations s.binary (operation s).1.binary (operation s).2)
    (reserve : (operation s).1.nodes ≤ s.nodes) :
    Rotations (plug fs s).binary (edit fs s operation).1.binary (edit fs s operation).2 ∧
      (edit fs s operation).2 = (operation s).2 ∧
      (edit fs s operation).1.nodes + (s.nodes - (operation s).1.nodes) = (plug fs s).nodes :=
  edit_spec fs s operation steps reserve

/-- Replacing the focus by another balanced subtree of the same height preserves
balance through every ancestor. Root contractions require separate handling. -/
theorem reassemble (fs : List Frame) {h : Nat} {t : Multiway}
    (ancestors : Valid h fs) (focus : Balanced h t) : Balanced (h + fs.length) (plug fs t) :=
  plug_balanced fs ancestors focus

end RotationBST.Geometric.Split.Multiway.Context.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Context.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Context.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract]
