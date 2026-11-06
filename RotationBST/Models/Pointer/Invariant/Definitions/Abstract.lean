module

public import RotationBST.Models.Pointer.Machine.Abstract

@[expose] public section
namespace RotationBST.Pointer

/-- A physical trace whose whole tree satisfies an invariant at every
instruction boundary, including both endpoints. -/
inductive TraceWithin (holds : Tree → Prop) : Config → Config → Nat → Prop where
  | refl {a : Config} : holds a.tree → TraceWithin holds a a 0
  | step {a b c : Config} {cost : Nat} : holds a.tree → Step a b →
      TraceWithin holds b c cost → TraceWithin holds a c (cost + 1)

end RotationBST.Pointer
