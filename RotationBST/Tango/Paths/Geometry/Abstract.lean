module

public import RotationBST.Tango.Paths.Abstract

@[expose] public section
namespace RotationBST.Tango

/-- Keys of a downward path starting at the root, in reference-depth order.
The empty path is allowed so a path can stop at any node. -/
inductive RootPath : Tree → Nat → List Nat → Prop where
  | empty (t : Tree) (lo : Nat) : RootPath t lo []
  | left {l r : Tree} {lo : Nat} {xs : List Nat} :
      RootPath l lo xs → RootPath (.node l r) lo ((lo + l.size) :: xs)
  | right {l r : Tree} {lo : Nat} {xs : List Nat} :
      RootPath r (lo + l.size + 1) xs → RootPath (.node l r) lo ((lo + l.size) :: xs)

/-- A downward path beginning anywhere in the fixed reference tree. -/
inductive ReferencePath : Tree → Nat → List Nat → Prop where
  | root {t : Tree} {lo : Nat} {xs : List Nat} : RootPath t lo xs → ReferencePath t lo xs
  | left {l r : Tree} {lo : Nat} {xs : List Nat} :
      ReferencePath l lo xs → ReferencePath (.node l r) lo xs
  | right {l r : Tree} {lo : Nat} {xs : List Nat} :
      ReferencePath r (lo + l.size + 1) xs → ReferencePath (.node l r) lo xs

/-- A subset is an interval within an ordered set of keys; gaps outside the
larger set are irrelevant. -/
def KeyInterval (inside outside : List Nat) : Prop :=
  ∀ a ∈ inside, ∀ b ∈ inside, ∀ x ∈ outside, a ≤ x → x ≤ b → x ∈ inside

end RotationBST.Tango
