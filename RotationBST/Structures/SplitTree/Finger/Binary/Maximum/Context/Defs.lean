module

public import RotationBST.Structures.SplitTree.Multiway.Context.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger
open Context

/-- An ancestor reached by following only last-child edges. -/
def IsRightFrame : Frame → Prop
  | .twoRight _ | .threeLast _ _ | .fourLast _ _ _ => True
  | _ => False

/-- The retained siblings of one ancestor, before any further enclosing keys. -/
def maximumFrameRemainder : Frame → Option Tree → Tree
  | .twoRight b, none => b.binary
  | .twoRight b, some rest => .node rest b.binary
  | .threeLast b c, none => .node b.binary c.binary
  | .threeLast b c, some rest => .node (.node rest b.binary) c.binary
  | .fourLast b c d, none => .node (.node b.binary c.binary) d.binary
  | .fourLast b c d, some rest => .node (.node (.node rest b.binary) c.binary) d.binary
  | _, _ => .nil

/-- The untouched smaller-key remainder of a last-child context. `none` means
that the focused interval is the whole tree. -/
def maximumContextRemainder : List Frame → Option Tree
  | [] => none
  | f :: fs => some (maximumFrameRemainder f (maximumContextRemainder fs))

/-- Concrete finger view of a focused interval with its enclosing context. -/
def maximumEnclosingView (focus : Multiway) (outer : List Frame) : Tree :=
  match maximumContextRemainder outer with
  | none => (maximumView focus).tree
  | some rest => maximumOpenView focus rest

end RotationBST.Arboral.Split.Multiway.Finger
