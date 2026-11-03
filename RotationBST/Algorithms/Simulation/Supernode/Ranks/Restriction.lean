module

public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Boundaries
public import RotationBST.Algorithms.Simulation.Supernode.Restriction

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- The end of an embedded segment is the position of the next parent key. -/
theorem segment_end (segment : Tree) (gaps : Nat → Tree) (offset lo first : Nat) :
    lo + first + gapWeight gaps offset first +
      (withGaps segment gaps (offset + first)).tree.size =
    lo + keyRank gaps offset (first + segment.size) := by
  rw [withGaps_tree_size, keyRank_shift]
  simp only [keyRank]
  omega

/-- Embedding any shape for a consecutive run of parent ranks gives precisely
those parent keys in its full-tree interval, including its external gaps. -/
theorem withGaps_segment_keys (shape segment : Tree) (gaps : Nat → Tree)
    (offset lo first : Nat) (fits : first + segment.size ≤ shape.size) :
    let start := lo + first + gapWeight gaps offset first
    Region.keys (withGaps segment gaps (offset + first)) start =
      Region.keys (withGaps shape gaps offset) lo ∩
        Finset.Ico start (start + (withGaps segment gaps (offset + first)).tree.size) := by
  dsimp only
  ext key
  rw [Finset.mem_inter, withGaps_keys, withGaps_keys, segment_end]
  constructor
  · rintro ⟨rank, bound, equal⟩
    have shifted := keyRank_shift gaps offset first rank
    have before := keyRank_strictMono gaps offset (show first + rank < first + segment.size by omega)
    refine ⟨⟨first + rank, by omega, by omega⟩, Finset.mem_Ico.mpr ⟨?_, by omega⟩⟩
    omega
  · rintro ⟨⟨rank, _, equal⟩, member⟩
    obtain ⟨lower, upper⟩ := Finset.mem_Ico.mp member
    have after : first ≤ rank := by
      by_contra notAfter
      have before := keyRank_before_gap gaps offset (show rank < first by omega)
      omega
    have before : rank < first + segment.size := by
      by_contra notBefore
      have later := (keyRank_strictMono gaps offset).monotone (show first + segment.size ≤ rank by omega)
      omega
    refine ⟨rank - first, by omega, ?_⟩
    have shifted := keyRank_shift gaps offset first (rank - first)
    rw [show first + (rank - first) = rank by omega] at shifted
    omega

/-- Every nonempty surviving run of parent keys is itself a canonical
supernode, independently of the shape chosen to represent that run. -/
theorem withGaps_segment_canonical {P : Finset Point}
    (shape segment : Tree) (gaps : Nat → Tree) (offset lo first : Nat)
    (canonical : Region.keys (withGaps shape gaps offset) lo =
      supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size))
    (fits : first + segment.size ≤ shape.size) (nonempty : 0 < segment.size) :
    let start := lo + first + gapWeight gaps offset first
    Region.keys (withGaps segment gaps (offset + first)) start =
      supernodeKeys P start (start + (withGaps segment gaps (offset + first)).tree.size) := by
  let start := lo + first + gapWeight gaps offset first
  have keys := withGaps_segment_keys shape segment gaps offset lo first fits
  change Region.keys (withGaps segment gaps (offset + first)) start = _ at keys ⊢
  rw [canonical] at keys
  have retained : (supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size) ∩
      Finset.Ico start (start + (withGaps segment gaps (offset + first)).tree.size)).Nonempty := by
    rw [← keys]
    exact ⟨start + keyRank gaps (offset + first) 0,
      (withGaps_keys segment gaps (offset + first) start _).mpr ⟨0, nonempty, rfl⟩⟩
  have weights := gapWeight_mono gaps offset (show first + segment.size + 1 ≤ shape.size + 1 by omega)
  have endBound : start + (withGaps segment gaps (offset + first)).tree.size ≤
      lo + (withGaps shape gaps offset).tree.size := by
    dsimp only [start]
    rw [segment_end, withGaps_tree_size]
    simp only [keyRank]
    omega
  exact keys.trans (supernodeKeys_restrict (by dsimp only [start]; omega) endBound retained).symm

end RotationBST.Geometric.Online.Supernode
