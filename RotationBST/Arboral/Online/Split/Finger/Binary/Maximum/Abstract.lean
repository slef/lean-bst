module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Abstract

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- A left spine with retained larger-key subtrees attached on the right. -/
def leftComb : List Tree → Tree → Tree
  | [], tail => tail
  | a :: rest, tail => .node (leftComb rest tail) a

structure MaximumView where
  spine : List Tree
  tail : Tree
  deriving DecidableEq, Repr

def MaximumView.tree (v : MaximumView) : Tree := leftComb v.spine v.tail

/-- Maximum-finger view retaining the ordinary encoding of all off-path trees. -/
def maximumView : Multiway → MaximumView
  | .nil => ⟨[], .nil⟩
  | .two a b => let v := maximumView b; ⟨v.spine ++ [v.tail], a.binary⟩
  | .three a b c => let v := maximumView c; ⟨v.spine ++ [v.tail, b.binary], a.binary⟩
  | .four a b c d => let v := maximumView d; ⟨v.spine ++ [v.tail, c.binary, b.binary], a.binary⟩

def maximumOpenView (t : Multiway) (rest : Tree) : Tree :=
  leftComb (maximumView t).spine (.node rest (maximumView t).tail)

def maximumOpenCost : Multiway → Nat
  | .nil => 0
  | .two _ b => maximumOpenCost b + 1
  | .three _ _ c => maximumOpenCost c + 2
  | .four _ _ _ d => maximumOpenCost d + 3

def maximumCost : Multiway → Nat
  | .nil => 0
  | .two _ b => maximumOpenCost b
  | .three _ _ c => maximumOpenCost c + 1
  | .four _ _ _ d => maximumOpenCost d + 1

end RotationBST.Arboral.Split.Multiway.Finger
