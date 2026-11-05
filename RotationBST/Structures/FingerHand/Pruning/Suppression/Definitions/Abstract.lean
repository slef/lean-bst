module

public import RotationBST.Structures.FingerHand.Pruning.Definitions.Abstract

@[expose] public section
namespace RotationBST.FingerHand

/-- Every retained vertex is marked or branches into two nonempty retained
regions. This is the local normal form of a compressed skeleton. -/
def Reduced (marks : Finset Nat) : LabelledTree Nat → Prop
  | .nil => True
  | .node l x r => Reduced marks l ∧ Reduced marks r ∧ (x ∈ marks ∨ l ≠ .nil ∧ r ≠ .nil)

/-- Suppress one obsolete vertex without creating another obsolete branch.
A unary vertex can always be contracted. Removing a leaf requires its parent
to remain marked. Enclosing vertices are retained. -/
inductive Suppress (marks : Finset Nat) (x : Nat) : LabelledTree Nat → LabelledTree Nat → Prop where
  | unaryLeft {t : LabelledTree Nat} : t ≠ .nil → Suppress marks x (.node t x .nil) t
  | unaryRight {t : LabelledTree Nat} : t ≠ .nil → Suppress marks x (.node .nil x t) t
  | leafLeft {r : LabelledTree Nat} {y : Nat} : y ∈ marks →
      Suppress marks x (.node (.node .nil x .nil) y r) (.node .nil y r)
  | leafRight {l : LabelledTree Nat} {y : Nat} : y ∈ marks →
      Suppress marks x (.node l y (.node .nil x .nil)) (.node l y .nil)
  | inLeft {a b r : LabelledTree Nat} {y : Nat} : Suppress marks x a b →
      Suppress marks x (.node a y r) (.node b y r)
  | inRight {a b l : LabelledTree Nat} {y : Nat} : Suppress marks x a b →
      Suppress marks x (.node l y a) (.node l y b)

end RotationBST.FingerHand
