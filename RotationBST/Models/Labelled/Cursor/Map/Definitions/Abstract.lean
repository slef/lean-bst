module

public import RotationBST.Models.Labelled.Cursor.Definitions.Abstract

@[expose] public section
namespace RotationBST

def LabelledTree.map {α β : Type} (f : α → β) : LabelledTree α → LabelledTree β
  | .nil => .nil
  | .node l entry r => .node (l.map f) (f entry) (r.map f)

namespace LabelledCursor

def Frame.map {α β : Type} (f : α → β) : Frame α → Frame β
  | .left entry r => .left (f entry) (r.map f)
  | .right l entry => .right (l.map f) (f entry)

/-- A proof projection of node fields, not a traversal run by the machine. -/
def Config.map {α β : Type} (f : α → β) (c : Config α) : Config β :=
  ⟨c.focus.map f, c.context.map (Frame.map f)⟩

end LabelledCursor
end RotationBST
