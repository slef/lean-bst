module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.LastTouch.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.LastTouch.Results

/-- A new row makes exactly its touched keys the most recent keys. -/
theorem row_update {n time : Nat} {P : Finset Point} (history : History n time P)
    (keys : Finset Nat) (key : Nat) :
    lastTouch (P ∪ row time keys) key = if key ∈ keys then (time : WithBot Nat) else lastTouch P key :=
  lastTouch_extend history keys key

/-- Every legal row touches the higher-priority boundaries of its touched keys.
Equal-priority keys are deliberately excluded: they belong to one supernode. -/
theorem parent_boundary {n time request boundary key : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (touched : key ∈ keys) (parent : LastTouchBoundary P boundary key) : boundary ∈ keys :=
  boundary_required history legal touched parent

end RotationBST.Geometric.Online.LastTouch.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.LastTouch.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.LastTouch.Results allowing [
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.LastTouch.Defs]
