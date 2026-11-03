module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Restriction

@[expose] public section
namespace RotationBST.Geometric.Online.LastTouch.Supernode.Results

/-- Every nonempty interval has a nonempty root supernode, including intervals
whose keys have never been touched. -/
theorem nonempty (P : Finset Point) {lo hi : Nat} (interval : lo < hi) :
    (supernodeKeys P lo hi).Nonempty := supernodeKeys_nonempty P interval

/-- A legal row reaching into a gap must touch its adjacent supernode boundary. -/
theorem parent {n time request lo hi boundary key : Nat}
    {P : Finset Point} {keys : Finset Nat} (history : History n time P)
    (legal : Completion n time request P keys) (touched : key ∈ keys)
    (gap : SupernodeGap P lo hi boundary key) : boundary ∈ keys :=
  supernode_gap_required history legal touched gap

/-- New touches, restricted to the interval, become precisely its new root
supernode. The definition and update use only the history and current row. -/
theorem row_update {n time lo hi : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (touched : (keys ∩ Finset.Ico lo hi).Nonempty) :
    supernodeKeys (P ∪ row time keys) lo hi = keys ∩ Finset.Ico lo hi :=
  supernode_row_keys history touched

/-- Restricting a supernode to an interval that retains an old root key
preserves exactly the root keys inside that interval. -/
theorem restriction {P : Finset Point} {lo hi first last : Nat}
    (lower : lo ≤ first) (upper : last ≤ hi)
    (retained : (supernodeKeys P lo hi ∩ Finset.Ico first last).Nonempty) :
    supernodeKeys P first last = supernodeKeys P lo hi ∩ Finset.Ico first last :=
  supernodeKeys_restrict lower upper retained

end RotationBST.Geometric.Online.LastTouch.Supernode.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.LastTouch.Supernode.Results`: 4 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.LastTouch.Supernode.Results allowing [
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.LastTouch.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Defs, RotationBST.Models.Region.View.Defs]
