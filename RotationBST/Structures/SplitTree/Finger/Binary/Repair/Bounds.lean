module

public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Open
public import RotationBST.Structures.SplitTree.Multiway.Edges.Bounds

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

theorem repairViewCost_bound (t : Multiway) : repairViewCost t ≤ 3 := by
  cases t with
  | nil => decide
  | two a b => cases a <;> cases b <;> simp [repairViewCost]
  | three a b c => cases a <;> cases b <;> simp [repairViewCost]
  | four a b c d => cases a <;> cases b <;> simp [repairViewCost]

theorem repairOpenCost_bound (t : Multiway) : repairOpenCost t ≤ 3 := by
  cases t with
  | nil => decide
  | two a b => cases a <;> cases b <;> simp [repairOpenCost, repairViewCost]
  | three a b c => exact repairViewCost_bound _
  | four a b c d => exact repairViewCost_bound _

end RotationBST.SplitTree.Multiway.Finger
