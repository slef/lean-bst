module

public import RotationBST.Structures.PopTart.Definitions.Abstract

@[expose] public section
namespace RotationBST.PopTart.Vanilla

/-- A right spine whose newly pushed fringe slot dominates the older mass.
The leaf case is an empty active stack with one nonnegative-weight fringe slot. -/
inductive Valid : WeightedTree → Prop where
  | leaf (t : Tree) (w : ℝ) (nonnegative : 0 ≤ w) : Valid (.leaf t w)
  | push {tail : WeightedTree} (t : Tree) (w : ℝ) (valid : Valid tail)
      (dominates : tail.mass ≤ w) : Valid (.node (.leaf t w) tail)

def push (t : Tree) (w : ℝ) (stack : WeightedTree) : WeightedTree :=
  .node (.leaf t w) stack

/-- Expose the top separator and its weighted fringe slot. The caller removes
that separator; the realizing pointer trace itself preserves the entire tree. -/
def pop : WeightedTree → Option ((Tree × ℝ) × WeightedTree)
  | .node (.leaf t w) tail => some ((t, w), tail)
  | _ => none

/-- The caller supplies a new top separator on push and takes the exposed top
separator on pop. Only rebalancing between those boundaries is charged here. -/
inductive Operation : WeightedTree → WeightedTree → Type where
  | push (t : Tree) (w : ℝ) (stack : WeightedTree) : Operation stack (push t w stack)
  | pop (stack tail : WeightedTree) (t : Tree) (w : ℝ)
      (exposed : pop stack = some ((t, w), tail)) : Operation stack tail

namespace Operation

def input {stack tail : WeightedTree} : Operation stack tail → Tree
  | .push t _ stack => .node t stack.tree
  | .pop stack _ _ _ _ => stack.tree

def output {stack tail : WeightedTree} : Operation stack tail → Tree
  | .push _ _ _ => tail.tree
  | .pop _ tail t _ _ => .node t tail.tree

def Realizes {stack tail : WeightedTree} (op : Operation stack tail) (cost : Nat) : Prop :=
  Pointer.Trace ⟨op.input, []⟩ ⟨op.output, []⟩ cost

end Operation
end RotationBST.PopTart.Vanilla
