module

public import RotationBST.Structures.TreeBuffer.Shared.Definitions.Abstract
public import RotationBST.Structures.TreeBuffer.Snapshot.Recording.Definitions.Abstract

@[expose] public section
namespace RotationBST.TreeBuffer.Snapshot.Recording.Refinement

/-- Finger 0 runs the local normalizer and finger 1 scans the buffer cells.
The represented data changes after each packet write. -/
def Represents (actual : Shared.State Nat 2) (model : State) : Prop :=
  actual.Valid model.data ∧ actual.tree.erase = model.control.cursor.tree ∧
  model.control.cursor.key? = some (actual.position 0) ∧ actual.position 1 = model.scan.position

end RotationBST.TreeBuffer.Snapshot.Recording.Refinement
