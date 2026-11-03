module

import RotationBST.Audit.Check
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Hierarchy.Results

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

end RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Hierarchy.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Hierarchy.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Split.Multiway.Finger.TwoEnded.Hierarchy.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs,
  RotationBST.Structures.SplitTree.Accounting.Abstract,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Defs]
