module

public import RotationBST.Models.Pointer.Machine.Abstract

@[expose] public section
namespace RotationBST.Pointer

/-- Navigation only, distinguished from rotations so a walk has a fixed tree. -/
inductive Move : Config → Config → Prop where
  | downLeft {a b r : Tree} {cs : List Frame} : Move ⟨.node (.node a b) r, cs⟩ ⟨.node a b, .left r :: cs⟩
  | downRight {l a b : Tree} {cs : List Frame} : Move ⟨.node l (.node a b), cs⟩ ⟨.node a b, .right l :: cs⟩
  | upLeft {a b r : Tree} {cs : List Frame} : Move ⟨.node a b, .left r :: cs⟩ ⟨.node (.node a b) r, cs⟩
  | upRight {a b l : Tree} {cs : List Frame} : Move ⟨.node a b, .right l :: cs⟩ ⟨.node l (.node a b), cs⟩

inductive Walk : Config → Config → Nat → Prop where
  | refl {c : Config} : Walk c c 0
  | step {a b c : Config} {k : Nat} : Move a b → Walk b c k → Walk a c (k + 1)

end RotationBST.Pointer
