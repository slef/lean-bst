module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Results

/-- Establish both endpoint views in one physical BST, with balanced side
sizes, at a cost linear in the input multiway height. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil) :
    (make h t).1.Valid ∧ Rotations t.binary (make h t).1.tree (make h t).2 ∧ (make h t).2 ≤ 20 * h :=
  ⟨make_valid valid nonempty, make_rotations h t valid nonempty, make_cost valid nonempty⟩

/-- The root's branch choice approximates the nearer endpoint within factor two.
Maintaining the size balance under splitting is a separate obligation. -/
theorem endpoint_choice {state : State} (valid : state.Valid) (rank : Nat) (existsKey : rank < state.size) :
    chosenDistance state rank + 1 ≤ 2 * (min rank (state.size - 1 - rank) + 1) :=
  chosenDistance_bound valid rank existsKey

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs]
