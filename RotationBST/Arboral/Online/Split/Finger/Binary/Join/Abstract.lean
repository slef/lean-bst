module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract
public import RotationBST.Arboral.Online.Split.Multiway.Join.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- Cost of attaching a taller right sibling while retaining the left finger
and an arbitrary enclosing separator. -/
def joinOpenCost : Nat → Multiway → Multiway → Nat
  | 0, _, _ => 0
  | _ + 1, _, .nil => 0
  | d + 1, l, .two a _ => 1 + joinOpenCost d l a
  | d + 1, l, .three a _ _ => 2 + joinOpenCost d l a
  | d + 1, l, .four a _ _ _ =>
      match (Join.joinLeft d l a).1 with
      | .stay _ => 3 + joinOpenCost d l a
      | .rise _ _ => 3 + joinOpenCost d l a + 1

/-- Cost without an enclosing separator. The recursive join carries the other
root children as its remainder. -/
def joinViewCost : Nat → Multiway → Multiway → Nat
  | 0, _, _ => 0
  | _ + 1, _, .nil => 0
  | d + 1, l, .two a _ | d + 1, l, .three a _ _ => joinOpenCost d l a
  | d + 1, l, .four a _ _ _ => 1 + joinOpenCost d l a

/-- Attach a sibling at least as tall as the focused interval. The computed
height includes root promotion; the counter is for the maintained finger view. -/
def attachRight (focusHeight siblingHeight : Nat) (focus sibling : Multiway) : Join.Result :=
  let result := Join.finish siblingHeight (Join.joinLeft (siblingHeight - focusHeight) focus sibling)
  { result with cost := joinViewCost (siblingHeight - focusHeight) focus sibling }

end RotationBST.Arboral.Split.Multiway.Finger
