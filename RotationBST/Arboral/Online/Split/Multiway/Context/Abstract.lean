module

public import RotationBST.Arboral.Online.Split.Multiway.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Context

/-- One ancestor with a selected child omitted. -/
inductive Frame where
  | twoLeft (right : Multiway)
  | twoRight (left : Multiway)
  | threeFirst (middle right : Multiway)
  | threeMiddle (left right : Multiway)
  | threeLast (left middle : Multiway)
  | fourFirst (second third fourth : Multiway)
  | fourSecond (first third fourth : Multiway)
  | fourThird (first second fourth : Multiway)
  | fourLast (first second third : Multiway)
  deriving DecidableEq, Repr

/-- Reattach the focused subtree without changing any sibling. -/
def Frame.fill : Frame → Multiway → Multiway
  | .twoLeft b, t => .two t b
  | .twoRight a, t => .two a t
  | .threeFirst b c, t => .three t b c
  | .threeMiddle a c, t => .three a t c
  | .threeLast a b, t => .three a b t
  | .fourFirst b c d, t => .four t b c d
  | .fourSecond a c d, t => .four a t c d
  | .fourThird a b d, t => .four a b t d
  | .fourLast a b c, t => .four a b c t

/-- Siblings all have the focused subtree's height. -/
def Frame.Valid (h : Nat) : Frame → Prop
  | .twoLeft b => Balanced h b
  | .twoRight a => Balanced h a
  | .threeFirst b c => Balanced h b ∧ Balanced h c
  | .threeMiddle a c => Balanced h a ∧ Balanced h c
  | .threeLast a b => Balanced h a ∧ Balanced h b
  | .fourFirst b c d => Balanced h b ∧ Balanced h c ∧ Balanced h d
  | .fourSecond a c d => Balanced h a ∧ Balanced h c ∧ Balanced h d
  | .fourThird a b d => Balanced h a ∧ Balanced h b ∧ Balanced h d
  | .fourLast a b c => Balanced h a ∧ Balanced h b ∧ Balanced h c

/-- Reassemble nearest-first ancestors. -/
def plug : List Frame → Multiway → Multiway
  | [], t => t
  | f :: fs, t => plug fs (f.fill t)

/-- Heights increase by one at each enclosing multiway node. -/
def Valid : Nat → List Frame → Prop
  | _, [] => True
  | h, f :: fs => f.Valid h ∧ Valid (h + 1) fs

/-- Perform a computed local edit and reassemble its entire enclosing tree. -/
def edit (fs : List Frame) (t : Multiway) (operation : Multiway → Multiway × Nat) : Multiway × Nat :=
  let result := operation t
  (plug fs result.1, result.2)

end RotationBST.Arboral.Split.Multiway.Context
