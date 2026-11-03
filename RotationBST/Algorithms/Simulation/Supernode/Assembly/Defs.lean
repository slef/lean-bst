module

public import RotationBST.Algorithms.Simulation.Supernode.Nested.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Select.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Defs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- Exposed row keys, with recursively represented subtrees at the holes. -/
inductive Assembly where
  | hole (state : Nested)
  | node (left right : Assembly)
  deriving Repr

def Assembly.region : Assembly → Region
  | .hole state => .hole state.tree
  | .node left right => .node left.region right.region

/-- Unlabelled shape of the exposed keys, excluding the retained children. -/
def Assembly.shape : Assembly → Tree
  | .hole _ => .nil
  | .node left right => .node left.shape right.shape

/-- Retained nested children in their full inorder sequence. -/
def Assembly.children : Assembly → List Nested
  | .hole state => [state]
  | .node left right => left.children ++ right.children

/-- Only the holes must already be canonical; the exposed keys will form the
new current-row supernode after all touched child regions are attached. -/
def Assembly.Valid (P : Finset Point) : Assembly → Nat → Prop
  | .hole state, lo => Represents P lo state
  | .node left right, lo => left.Valid P lo ∧ right.Valid P (lo + left.region.tree.size + 1)

/-- Turn a split hierarchy into actual retained nested intervals. A leaf with
no parent keys is the original child gap, rather than an empty full BST. -/
def assemblePartition : Partitioned → List Nested → Nat → Assembly
  | .leaf none, children, first => .hole ((children[first]?).getD .empty)
  | .leaf (some state), children, first => .hole (retainedNested state children first)
  | .branch left right, children, first =>
      .node (assemblePartition left children first)
        (assemblePartition right children (first + left.tree.size + 1))

/-- Expose precisely this row's parent ranks, retaining other parent intervals
and the original children. Recursive child extraction follows this stage. -/
def selectParent (state : State) (children : List Nested) (lo : Nat) (keys : Finset Nat) : Assembly × Nat :=
  let ranks := touchedRanks state.tree.size
    (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 lo keys
  let selected := selectKeys (some state) ranks
  (assemblePartition selected.1 children 0, selected.2)

/-- Attach recursively extracted child regions at their absolute offsets,
accumulating the rotations performed inside the original holes. -/
def Assembly.fill (expand : Nested → Nat → Assembly × Nat) : Assembly → Nat → Assembly × Nat
  | .hole state, lo => expand state lo
  | .node left right, lo =>
      let l := left.fill expand lo
      let r := right.fill expand (lo + left.region.tree.size + 1)
      (.node l.1 r.1, l.2 + r.2)

end RotationBST.Arboral.Online.Supernode
