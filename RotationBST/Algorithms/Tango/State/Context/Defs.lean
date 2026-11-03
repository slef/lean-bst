module

public import RotationBST.Algorithms.Tango.State.Defs

@[expose] public section
namespace RotationBST.Tango.Context

/-- An ancestor frame, with the focused child's mark listed first. -/
inductive Frame where
  | left (sibling : MarkedTree) (cutFocus cutSibling : Bool)
  | right (sibling : MarkedTree) (cutFocus cutSibling : Bool)
  deriving DecidableEq, Repr

def Frame.fill : Frame → MarkedTree → MarkedTree
  | .left r cl cr, s => .node s r cl cr
  | .right l cr cl, s => .node l s cl cr

def Frame.marked : Frame → Bool
  | .left _ mark _ => mark
  | .right _ mark _ => mark

/-- Change only the mark on the focused child edge. -/
def Frame.setMark : Frame → Bool → Frame
  | .left r _ cr, mark => .left r mark cr
  | .right l _ cl, mark => .right l mark cl

/-- Reassemble the whole marked tree; the nearest ancestor is first. -/
def plug : List Frame → MarkedTree → MarkedTree
  | [], s => s
  | f :: fs, s => plug fs (f.fill s)

/-- Absolute offset of a frame's focused child, given its parent's offset. -/
def Frame.offset : Frame → Nat → Nat
  | .left _ _ _, lo => lo
  | .right l _ _, lo => lo + l.tree.size + 1

/-- Absolute offset of the focused subtree in a reassembled context. -/
def offset : List Frame → Nat → Nat
  | [], lo => lo
  | f :: fs, lo => f.offset (offset fs lo)

/-- The focused subtree starts an auxiliary component (or is the whole tree). -/
def Boundary : List Frame → Prop
  | [] => True
  | f :: _ => f.marked = true

end RotationBST.Tango.Context
