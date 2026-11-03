module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Restriction

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode.Ranks.Results

/-- Every supernode rank has a distinct full-tree position, even when arbitrary
subtrees occupy its gaps. -/
theorem ordered (gaps : Nat → Tree) (offset : Nat) : StrictMono (keyRank gaps offset) :=
  keyRank_strictMono gaps offset

/-- Current row touches pull back exactly to supernode ranks; gap keys are
excluded, and the selected ranks are charged injectively to touched keys. -/
theorem selection (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat) (keys : Finset Nat) :
    (touchedRanks shape.size gaps offset lo keys).image (fun rank => lo + keyRank gaps offset rank) =
      keys ∩ Region.keys (withGaps shape gaps offset) lo ∧
    (touchedRanks shape.size gaps offset lo keys).card =
      (keys ∩ Region.keys (withGaps shape gaps offset) lo).card ∧
    (touchedRanks shape.size gaps offset lo keys).card ≤ keys.card :=
  ⟨touchedRanks_image shape gaps offset lo keys, touchedRanks_card shape gaps offset lo keys,
    touchedRanks_card_le shape gaps offset lo keys⟩

/-- A row entering gap `i` touches both adjacent parent keys that exist.
The statement allows arbitrary trees in the gaps and any parent key shape. -/
theorem boundaries {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (shape : Tree) (gaps : Nat → Tree) (offset lo i key : Nat)
    (canonical : Region.keys (withGaps shape gaps offset) lo =
      supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size))
    (gapIndex : i ≤ shape.size)
    (lower : lo + i + gapWeight gaps offset i ≤ key)
    (upper : key < lo + i + gapWeight gaps offset i + (gaps (offset + i)).size)
    (touched : key ∈ keys) :
    (0 < i → lo + keyRank gaps offset (i - 1) ∈ keys) ∧
    (i < shape.size → lo + keyRank gaps offset i ∈ keys) := by
  constructor
  · intro positive
    have previous : i - 1 + 1 = i := by omega
    apply gap_left_required history legal shape gaps offset lo (i - 1) key canonical (by omega)
    · simpa only [previous] using lower
    · simpa only [previous] using upper
    · exact touched
  · intro parent
    exact gap_right_required history legal shape gaps offset lo i key canonical parent lower upper touched

/-- A nonempty consecutive run of parent keys, with all its attached gaps,
remains canonical when represented by any shape of the required size. -/
theorem retained_interval {P : Finset Point}
    (shape segment : Tree) (gaps : Nat → Tree) (offset lo first : Nat)
    (canonical : Region.keys (withGaps shape gaps offset) lo =
      supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size))
    (fits : first + segment.size ≤ shape.size) (nonempty : 0 < segment.size) :
    let start := lo + first + gapWeight gaps offset first
    Region.keys (withGaps segment gaps (offset + first)) start =
      supernodeKeys P start (start + (withGaps segment gaps (offset + first)).tree.size) :=
  withGaps_segment_canonical shape segment gaps offset lo first canonical fits nonempty

end RotationBST.Geometric.Online.Supernode.Ranks.Results

/-- info: abstract audit passed for `RotationBST.Geometric.Online.Supernode.Ranks.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Geometric.Online.Supernode.Ranks.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Region.Abstract,
  RotationBST.Algorithms.Simulation.Supernode.Embedding.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Ranks.Defs,
  RotationBST.Models.Geometric.Definitions.Abstract, RotationBST.Models.Region.View.Abstract,
  RotationBST.Algorithms.Simulation.LastTouch.Defs,
  RotationBST.Algorithms.Simulation.Supernode.Defs]
