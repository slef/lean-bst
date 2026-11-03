module

public import RotationBST.Structures.SplitTree.Finger.Locate.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger
open Context

/-- An ancestor reached by following only first-child edges. -/
def IsLeftFrame : Frame → Prop
  | .twoLeft _ | .threeFirst _ _ | .fourFirst _ _ _ => True
  | _ => False

/-- The retained siblings of one ancestor, before any further enclosing keys. -/
def frameRemainder : Frame → Option Tree → Tree
  | .twoLeft b, none => b.binary
  | .twoLeft b, some rest => .node b.binary rest
  | .threeFirst b c, none => .node b.binary c.binary
  | .threeFirst b c, some rest => .node b.binary (.node c.binary rest)
  | .fourFirst b c d, none => .node b.binary (.node c.binary d.binary)
  | .fourFirst b c d, some rest => .node b.binary (.node c.binary (.node d.binary rest))
  | _, _ => .nil

/-- The untouched larger-key remainder of a first-child context. `none` means
that the focused interval is the whole tree. -/
def contextRemainder : List Frame → Option Tree
  | [] => none
  | f :: fs => some (frameRemainder f (contextRemainder fs))

/-- Concrete finger view of a focused interval with its enclosing context. -/
def enclosingView (focus : Multiway) (outer : List Frame) : Tree :=
  match contextRemainder outer with
  | none => (binaryView focus).tree
  | some rest => openView focus rest

end RotationBST.SplitTree.Multiway.Finger
