module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Hierarchy.Results

/-- Execute any complete split hierarchy from a valid shared interval. The
rotation count includes all splits and normalization of their outputs. -/
theorem realize (hierarchy : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = hierarchy.size) :
    Rotations (intervalTree input) hierarchy (hierarchyCost hierarchy input) ∧
      hierarchyCost hierarchy input ≤ 6014 * hierarchy.size :=
  ⟨hierarchy_rotations hierarchy input valid sizes, hierarchy_linear hierarchy input valid sizes⟩

/-- The initial node reserve and smaller-side charges pay every recursive split. -/
theorem accounting (hierarchy : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = hierarchy.size) :
    hierarchyCost hierarchy input ≤ 14 * intervalNodes input + 3000 * totalCharge hierarchy :=
  hierarchy_credit hierarchy input valid sizes

/-- Initialization from a balanced multiway tree costs at most six rotations
per level, in addition to the hierarchy's linear total cost. -/
theorem construction {h : Nat} {t : Multiway} (valid : Balanced h t)
    (nonempty : t ≠ .nil) (hierarchy : Tree) (sizes : t.size = hierarchy.size) :
    Rotations t.binary hierarchy
      ((fromRoot h t).2 + hierarchyCost hierarchy (some (fromRoot h t).1)) ∧
      (fromRoot h t).2 + hierarchyCost hierarchy (some (fromRoot h t).1) ≤
        6014 * hierarchy.size + 6 * h :=
  hierarchy_from_balanced valid nonempty hierarchy sizes

end RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Hierarchy.Results

#check_bst_abstract RotationBST.Arboral.Split.Multiway.Finger.TwoEnded.Hierarchy.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Abstract,
  RotationBST.Arboral.Online.Split.Accounting.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Abstract]
