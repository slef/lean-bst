module

public import RotationBST.Tango.State.Nesting.Abstract

@[expose] public section
namespace RotationBST.Tango.ComponentNesting

/-- Group consecutive fringe slots into a new attached component. Cutting
active key ranks `[i,j)` groups `j - i + 1` slots, starting at slot `i`. -/
def group : ComponentNesting → Nat → Nat → ComponentNesting
  | .empty, _, _ => .empty
  | .branch children, first, count => .branch
      (children.take first ++ [.branch ((children.drop first).take count)] ++ children.drop (first + count))

/-- Merge one attached component into its parent by expanding its fringe slots. -/
def merge : ComponentNesting → Nat → ComponentNesting
  | .empty, _ => .empty
  | .branch children, i =>
      match children[i]? with
      | none => .branch children
      | some child => .branch (children.take i ++ child.fringe ++ children.drop (i + 1))

/-- One nontrivial interval cut, expressed without choosing an auxiliary
binary shape. The remaining parent component must also be nonempty. -/
inductive Cut : ComponentNesting → ComponentNesting → Prop where
  | interval (before middle after : List ComponentNesting)
      (nonempty : 2 ≤ middle.length) (remaining : 0 < before.length + after.length) :
      Cut (.branch (before ++ middle ++ after)) (.branch (before ++ [.branch middle] ++ after))

end RotationBST.Tango.ComponentNesting
