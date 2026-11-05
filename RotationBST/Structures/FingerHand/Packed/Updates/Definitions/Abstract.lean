module

public import RotationBST.Structures.FingerHand.Packed.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand.Hand

/-- Insert a pseudofinger above `child`, keeping its off-path sibling as a
knuckle and its incoming tendon explicit. -/
def graft (cs : List Pointer.Frame) (d : Tendon.State) (f : Pointer.Frame) (child : Hand) : Hand :=
  match f with
  | .left g => .node cs d child (.knuckle g)
  | .right g => .node cs d (.knuckle g) child

/-- An exposed pseudofinger with no incoming tendon. -/
def fork (left right : Hand) : Hand := .node [] (Tendon.State.ofPath []) left right

/-- Rotate two exposed neighboring pseudofingers. Their child regions and the
incoming tendon of the rotated region stay intact. -/
inductive LocalRotation : Hand → Hand → Prop where
  | right (cs : List Pointer.Frame) (d : Tendon.State) (a b c : Hand) :
      LocalRotation (.node cs d (fork a b) c) (.node cs d a (fork b c))
  | left (cs : List Pointer.Frame) (d : Tendon.State) (a b c : Hand) :
      LocalRotation (.node cs d a (fork b c)) (.node cs d (fork a b) c)

/-- A local expansion retains the reference tree and every existing
pseudofinger, adding exactly one pseudofinger. It is a representation change,
not an insertion into the underlying BST's key universe. -/
structure Expansion (before after : Hand) : Prop where
  before_valid : before.Valid
  after_valid : after.Valid
  reference : after.reference = before.reference
  count : after.count = before.count + 1
  keys : ∀ lo, (before.labels lo).inorder.Sublist (after.labels lo).inorder

/-- An enclosing pseudofinger and the sibling region not being edited. -/
inductive ContextFrame where
  | left (path : List Pointer.Frame) (tendon : Tendon.State) (right : Hand)
  | right (path : List Pointer.Frame) (tendon : Tendon.State) (left : Hand)

namespace Context

def plug : List ContextFrame → Hand → Hand
  | [], h => h
  | .left cs d r :: fs, h => plug fs (.node cs d h r)
  | .right cs d l :: fs, h => plug fs (.node cs d l h)

def Valid : List ContextFrame → Prop
  | [] => True
  | .left cs d r :: fs => d.Represents cs ∧ r.Valid ∧ Valid fs
  | .right cs d l :: fs => d.Represents cs ∧ l.Valid ∧ Valid fs

/-- The actual pointer zipper of the edited region within the represented BST. -/
def pointer : List ContextFrame → List Pointer.Frame
  | [] => []
  | .left _ d r :: fs => (.left r.tree :: d.context) ++ pointer fs
  | .right _ d l :: fs => (.right l.tree :: d.context) ++ pointer fs

/-- The same enclosing region in the uncompressed reference tree. -/
def referencePath : List ContextFrame → List Pointer.Frame
  | [] => []
  | .left cs _ r :: fs => (.left r.reference :: cs) ++ referencePath fs
  | .right cs _ l :: fs => (.right l.reference :: cs) ++ referencePath fs

def potential : List ContextFrame → Nat
  | [] => 0
  | .left _ d r :: fs => d.potential + r.potential + potential fs
  | .right _ d l :: fs => d.potential + l.potential + potential fs

def count : List ContextFrame → Nat
  | [] => 0
  | .left _ _ r :: fs => 1 + r.count + count fs
  | .right _ _ l :: fs => 1 + l.count + count fs

end Context
end RotationBST.FingerHand.Hand
