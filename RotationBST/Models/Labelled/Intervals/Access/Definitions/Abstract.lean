module

public import RotationBST.Models.Labelled.Cursor.Definitions.Abstract
public import RotationBST.Models.Labelled.Intervals.Definitions.Abstract
public import RotationBST.Models.Pointer.Routing.Definitions.Abstract

@[expose] public section
namespace RotationBST.IntervalMetadata.Access

/-- Read the actual key and interval words, then choose a neighboring link.
The successful charge is three word reads plus one pointer move. -/
def route (target : Nat) (c : LabelledCursor.Config (Nat × Bounds)) :
    Option (Nat × LabelledCursor.Config (Nat × Bounds)) := do
  let (key, bounds) ← c.read
  let direction ← Pointer.Routing.choose ⟨bounds.low, key, bounds.high⟩ target
  let next ← match direction with
    | .left => LabelledCursor.perform .downLeft c
    | .right => LabelledCursor.perform .downRight c
    | .parent => match c.context with
      | .left _ _ :: _ => LabelledCursor.perform .upLeft c
      | .right _ _ :: _ => LabelledCursor.perform .upRight c
      | [] => none
  return (4, next)

def Canonical (c : LabelledCursor.Config (Nat × Bounds)) : Prop :=
  c.tree = label c.tree.erase 0

end RotationBST.IntervalMetadata.Access
