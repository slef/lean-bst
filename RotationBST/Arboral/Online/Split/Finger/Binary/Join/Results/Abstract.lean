module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.Binary.Join.Balance

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.Join.Results

/-- Attach a taller sibling while keeping the minimum finger, at cost linear
in the height difference rather than the height of the enclosing tree. -/
theorem attach {hl hr : Nat} {l r : Multiway}
    (left : Balanced hl l) (right : Balanced hr r) (ordered : hl ≤ hr) :
    let result := attachRight hl hr l r
    Rotations (openView l r.binary) (binaryView result.tree).tree result.cost ∧
      Balanced result.height result.tree ∧ result.cost ≤ 4 * (hr - hl) ∧
      hr ≤ result.height ∧ result.height ≤ hr + 1 :=
  ⟨attachRight_rotations _ _ _ _, (attachRight_balance left right ordered).1,
    attachRight_cost _ _ _ _, (attachRight_balance left right ordered).2⟩

/-- The same repair composes with an arbitrary enclosing separator and remainder. -/
theorem before_remainder (hl hr : Nat) (l r : Multiway) (rest : Tree) :
    Rotations (openView l (.node r.binary rest)) (openView (attachRight hl hr l r).tree rest)
      (joinOpenCost (hr - hl) l r) ∧ joinOpenCost (hr - hl) l r ≤ 4 * (hr - hl) :=
  ⟨attachRight_open _ _ _ _ _, joinOpen_cost _ _ _⟩

end RotationBST.Arboral.Split.Multiway.Finger.Join.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.Join.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Join.Abstract]
