module

public import RotationBST.Algorithms.Simulation.Supernode.Layer.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Initialize.Defs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode
open Split.Multiway.Finger.TwoEnded

/-- A supernode stores a shared split state and one recursively represented
subtree for each external gap, in inorder. -/
inductive Nested where
  | empty
  | layer (state : State) (children : List Nested)
  deriving Repr

def Nested.tree : Nested → Tree
  | .empty => .nil
  | .layer state children =>
      (withGaps state.tree (fun i => ((children.map Nested.tree)[i]?).getD .nil) 0).tree

/-- Full-tree realization of the current supernode's active region. -/
def nestedRegion (state : State) (children : List Nested) : Region :=
  withGaps state.tree (fun i => ((children.map Nested.tree)[i]?).getD .nil) 0

/-- Recursively represented canonical supernodes, with exact child offsets.
The invariant stores only current history; it contains no future requests. -/
inductive Represents (P : Finset Point) : Nat → Nested → Prop where
  | empty (lo : Nat) : Represents P lo .empty
  | layer (lo : Nat) (state : State) (children : List Nested)
      (balanced : state.HeightValid)
      (arity : children.length = state.size + 1)
      (canonical : Region.keys (nestedRegion state children) lo =
        supernodeKeys P lo (lo + (nestedRegion state children).tree.size))
      (subtrees : ∀ i : Fin children.length,
        Represents P
          (lo + i.val + gapWeight (fun j => ((children.map Nested.tree)[j]?).getD .nil) 0 i.val)
          children[i]) :
      Represents P lo (.layer state children)

/-- Initially all keys are untouched and belong to one bottom-priority layer. -/
def initialNested (n : Nat) : Nested :=
  match initialInterval n with
  | none => .empty
  | some state => .layer state (List.replicate (state.size + 1) .empty)

/-- Retain a consecutive run of parent keys in a new shared representation,
carrying along exactly its external child gaps. -/
def retainedNested (state : State) (children : List Nested) (first : Nat) : Nested :=
  .layer state ((children.drop first).take (state.size + 1))

end RotationBST.Geometric.Online.Supernode
