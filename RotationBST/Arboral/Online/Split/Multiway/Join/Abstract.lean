module

public import RotationBST.Arboral.Online.Split.Multiway.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Join

/-- A subtree either fits at its old height or promotes a separator between
 two children of that height. -/
inductive Promotion where
  | stay (tree : Multiway)
  | rise (left right : Multiway)
  deriving DecidableEq, Repr

def Promotion.tree : Promotion → Multiway
  | .stay t => t
  | .rise l r => .two l r

def Promotion.Valid (h : Nat) : Promotion → Prop
  | .stay t => Balanced h t
  | .rise l r => Balanced h l ∧ Balanced h r

/-- Join across a separator, descending the taller left tree's right spine.
The height difference is supplied explicitly. Overflow propagates upward. -/
def joinRight : Nat → Multiway → Multiway → Promotion × Nat
  | 0, l, r => (.rise l r, 0)
  | _ + 1, .nil, r => (.stay (.two .nil r), 0)
  | d + 1, .two a b, r =>
      match joinRight d b r with
      | (.stay t, cost) => (.stay (.two a t), cost + 1)
      | (.rise x y, cost) => (.stay (.three a x y), cost + 1)
  | d + 1, .three a b c, r =>
      match joinRight d c r with
      | (.stay t, cost) => (.stay (.three a b t), cost + 2)
      | (.rise x y, cost) => (.stay (.four a b x y), cost + 3)
  | d + 1, .four a b c e, r =>
      match joinRight d e r with
      | (.stay t, cost) => (.stay (.four a b c t), cost + 2)
      | (.rise x y, cost) => (.rise (.two a b) (.three c x y), cost + 2)

/-- Finish any root promotion after joining. -/
def appendRight (difference : Nat) (left right : Multiway) : Multiway × Nat :=
  let result := joinRight difference left right
  (result.1.tree, result.2)

/-- Symmetric join, descending the taller right tree's left spine. -/
def joinLeft : Nat → Multiway → Multiway → Promotion × Nat
  | 0, l, r => (.rise l r, 0)
  | _ + 1, l, .nil => (.stay (.two l .nil), 0)
  | d + 1, l, .two a b =>
      match joinLeft d l a with
      | (.stay t, cost) => (.stay (.two t b), cost + 1)
      | (.rise x y, cost) => (.stay (.three x y b), cost + 2)
  | d + 1, l, .three a b c =>
      match joinLeft d l a with
      | (.stay t, cost) => (.stay (.three t b c), cost + 1)
      | (.rise x y, cost) => (.stay (.four x y b c), cost + 1)
  | d + 1, l, .four a b c e =>
      match joinLeft d l a with
      | (.stay t, cost) => (.stay (.four t b c e), cost + 2)
      | (.rise x y, cost) => (.rise (.three x y b) (.two c e), cost + 3)

def appendLeft (difference : Nat) (left right : Multiway) : Multiway × Nat :=
  let result := joinLeft difference left right
  (result.1.tree, result.2)

/-- The resulting tree, its computed height, and exact rotation count. -/
structure Result where
  tree : Multiway
  height : Nat
  cost : Nat
  deriving DecidableEq, Repr

def finish (baseHeight : Nat) (result : Promotion × Nat) : Result :=
  match result with
  | (.stay t, cost) => ⟨t, baseHeight, cost⟩
  | (.rise l r, cost) => ⟨.two l r, baseHeight + 1, cost⟩

/-- Join two balanced trees across one separator. The supplied heights determine
which spine to follow; the result records any increase from root promotion. -/
def run (leftHeight rightHeight : Nat) (left right : Multiway) : Result :=
  if rightHeight ≤ leftHeight then
    finish leftHeight (joinRight (leftHeight - rightHeight) left right)
  else finish rightHeight (joinLeft (rightHeight - leftHeight) left right)

end RotationBST.Arboral.Split.Multiway.Join
