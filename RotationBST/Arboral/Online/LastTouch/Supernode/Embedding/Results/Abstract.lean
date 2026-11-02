module

import RotationBST.AbstractAudit.Check
public import RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Proofs
public import RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Proofs

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

#check_bst_abstract RotationBST.Arboral.Online.Supernode.Embedding.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Arboral.Online.Split.Multiway.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Context.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Edges.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Join.Compact.Abstract,
  RotationBST.Arboral.Online.Split.Multiway.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Repair.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Conversion.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Binary.Maximum.Join.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Locate.Split.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Frame.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Repair.Context.Abstract,
  RotationBST.Arboral.Online.Split.Finger.Maximum.Partition.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Height.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Expose.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Normalize.Abstract,
  RotationBST.Arboral.Online.Split.Accounting.Abstract,
  RotationBST.Arboral.Online.Split.Finger.TwoEnded.Hierarchy.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Arboral.Online.LastTouch.Supernode.Embedding.Abstract]
