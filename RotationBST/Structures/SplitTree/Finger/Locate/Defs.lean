module

public import RotationBST.Structures.SplitTree.Finger.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- A containing interval and the untouched nearest-first enclosing ancestors. -/
structure Location where
  focus : Multiway
  height : Nat
  outer : List Context.Frame
  deriving DecidableEq, Repr

/-- Ascend from the minimum until the requested rank lies in the local interval. -/
def locate (t : Multiway) (rank : Nat) : Location :=
  let levels := searchLevels t rank
  ⟨Context.plug ((leftSpine t).take levels) .nil, levels, (leftSpine t).drop levels⟩

end RotationBST.Arboral.Split.Multiway.Finger
