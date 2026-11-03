module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Maximum.Join.Results

/-- Joining a shortened maximum interval to a taller left sibling preserves
its finger view, with cost proportional to the height difference. -/
theorem attach {hf hs : Nat} {focus sibling : Multiway}
    (focused : Balanced hf focus) (retained : Balanced hs sibling) (ordered : hf ≤ hs) :
    let result := attachLeft hf hs focus sibling
    Balanced result.height result.tree ∧ hs ≤ result.height ∧ result.height ≤ hs + 1 ∧
      Rotations (maximumOpenView focus sibling.binary) (maximumView result.tree).tree result.cost ∧
      result.cost ≤ 4 * (hs - hf) :=
  ⟨(attachLeft_balance focused retained ordered).1,
    (attachLeft_balance focused retained ordered).2.1,
    (attachLeft_balance focused retained ordered).2.2,
    attachLeft_rotations hf hs focus sibling, attachLeft_cost hf hs focus sibling⟩

/-- The same attachment retains an arbitrary further enclosing remainder. -/
theorem attach_open (hf hs : Nat) (focus sibling : Multiway) (rest : Tree) :
    Rotations (maximumOpenView focus (.node rest sibling.binary))
      (maximumOpenView (attachLeft hf hs focus sibling).tree rest)
      (maximumJoinOpenCost (hs - hf) sibling focus) ∧
      maximumJoinOpenCost (hs - hf) sibling focus ≤ 4 * (hs - hf) :=
  ⟨attachLeft_open hf hs focus sibling rest, maximumJoinOpen_cost _ _ _⟩

end RotationBST.Arboral.Split.Multiway.Finger.Maximum.Join.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Maximum.Join.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs]
