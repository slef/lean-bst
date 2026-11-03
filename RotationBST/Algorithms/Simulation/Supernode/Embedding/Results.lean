module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Proofs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode.Embedding.Results
open Split.Multiway.Finger.TwoEnded

/-- Rotations inside a supernode retain all gap subtrees in order, at exactly
the original cost. The gaps may have arbitrary shapes and sizes. -/
theorem lift {s t : Tree} {cost : Nat} (steps : Rotations s t cost)
    (gaps : Nat → Tree) (offset : Nat) :
    Rotations (withGaps s gaps offset).tree (withGaps t gaps offset).tree cost ∧
      (withGaps s gaps offset).fringe = (withGaps t gaps offset).fringe :=
  withGaps_rotations steps gaps offset

/-- A complete shared split exposes the corresponding full-tree key, with
unchanged rotation cost despite arbitrary untouched subtrees in its gaps. -/
theorem split_access {state : State} (valid : state.HeightValid)
    (rank : Nat) (existsKey : rank < state.size) (gaps : Nat → Tree) (offset : Nat) :
    Access (withGaps state.tree gaps offset).tree (withGaps (split state rank).tree gaps offset).tree
      (keyRank gaps offset rank) (split state rank).cost :=
  withGaps_access (Split.Multiway.Finger.TwoEnded.split_access valid rank existsKey) gaps offset

/-- A whole split hierarchy costs linearly in supernode keys, independently
of how many ordinary BST keys lie in its untouched gaps. -/
theorem hierarchy (shape : Tree) (input : Option State)
    (valid : IntervalValid input) (sizes : (intervalTree input).size = shape.size)
    (gaps : Nat → Tree) (offset : Nat) :
    Rotations (withGaps (intervalTree input) gaps offset).tree (withGaps shape gaps offset).tree
      (hierarchyCost shape input) ∧ hierarchyCost shape input ≤ 6014 * shape.size :=
  ⟨(withGaps_rotations (hierarchy_rotations shape input valid sizes) gaps offset).1,
    hierarchy_linear shape input valid sizes⟩

end RotationBST.Arboral.Online.Supernode.Embedding.Results

/-- info: abstract audit passed for `RotationBST.Arboral.Online.Supernode.Embedding.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Arboral.Online.Supernode.Embedding.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Structures.SplitTree.Multiway.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Context.Abstract,
  RotationBST.Structures.SplitTree.Multiway.Edges.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Defs,
  RotationBST.Structures.SplitTree.Multiway.Join.Compact.Defs,
  RotationBST.Structures.SplitTree.Multiway.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Abstract,
  RotationBST.Structures.SplitTree.Finger.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Embedding.Defs,
  RotationBST.Structures.SplitTree.Finger.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Abstract,
  RotationBST.Structures.SplitTree.Finger.Binary.Repair.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Join.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Locate.Split.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Frame.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Repair.Context.Defs,
  RotationBST.Structures.SplitTree.Finger.Maximum.Partition.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Height.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Expose.Defs,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Normalize.Defs,
  RotationBST.Structures.SplitTree.Accounting.Abstract,
  RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Defs,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs]
