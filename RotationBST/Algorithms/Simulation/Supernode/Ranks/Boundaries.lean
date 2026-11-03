module

public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Proofs
public import RotationBST.Algorithms.Simulation.Supernode.Proofs

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode

/-- A parent key preceding gap `i` lies strictly before that gap. -/
theorem keyRank_before_gap (gaps : Nat → Tree) (offset : Nat) {j i : Nat}
    (before : j < i) : keyRank gaps offset j < i + gapWeight gaps offset i := by
  have weights := gapWeight_mono gaps offset (show j + 1 ≤ i by omega)
  simp only [keyRank]
  omega

/-- The right endpoint of a gap is the following parent key. -/
theorem gap_end (gaps : Nat → Tree) (offset i : Nat) :
    i + gapWeight gaps offset i + (gaps (offset + i)).size = keyRank gaps offset i := by
  have append := gapWeight_add gaps offset i 1
  have single : gapWeight gaps (offset + i) 1 = (gaps (offset + i)).size := by
    simp [gapWeight]
  rw [single] at append
  simp only [keyRank]
  omega

/-- Touching inside a gap forces its right parent boundary, when present,
to be touched in the same satisfied row. -/
theorem gap_right_required {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (shape : Tree) (gaps : Nat → Tree) (offset lo i key : Nat)
    (canonical : Region.keys (withGaps shape gaps offset) lo =
      supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size))
    (parent : i < shape.size)
    (lower : lo + i + gapWeight gaps offset i ≤ key)
    (upper : key < lo + i + gapWeight gaps offset i + (gaps (offset + i)).size)
    (touched : key ∈ keys) : lo + keyRank gaps offset i ∈ keys := by
  have rightEnd := gap_end gaps offset i
  have root : lo + keyRank gaps offset i ∈ Region.keys (withGaps shape gaps offset) lo :=
    (withGaps_keys shape gaps offset lo _).mpr ⟨i, parent, rfl⟩
  have rootBounds := Finset.mem_Ico.mp (Finset.mem_filter.mp
    (show lo + keyRank gaps offset i ∈ supernodeKeys P lo
      (lo + (withGaps shape gaps offset).tree.size) from canonical ▸ root)).1
  apply supernode_gap_required history legal touched
  refine ⟨canonical ▸ root, by omega, by omega, by omega, ?_⟩
  intro y below above different member
  rw [← canonical] at member
  obtain ⟨j, _, equal⟩ := (withGaps_keys shape gaps offset lo y).mp member
  by_cases before : j < i
  · have bound := keyRank_before_gap gaps offset before
    have : min (lo + keyRank gaps offset i) key = key := by omega
    rw [this] at below
    omega
  · by_cases same : j = i
    · subst j
      exact different equal
    · have bound := keyRank_strictMono gaps offset (show i < j by omega)
      have : max (lo + keyRank gaps offset i) key = lo + keyRank gaps offset i := by omega
      rw [this] at above
      omega

/-- The left boundary is also required; the first gap has no left boundary. -/
theorem gap_left_required {n time request : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (shape : Tree) (gaps : Nat → Tree) (offset lo i key : Nat)
    (canonical : Region.keys (withGaps shape gaps offset) lo =
      supernodeKeys P lo (lo + (withGaps shape gaps offset).tree.size))
    (parent : i < shape.size)
    (lower : lo + (i + 1) + gapWeight gaps offset (i + 1) ≤ key)
    (upper : key < lo + (i + 1) + gapWeight gaps offset (i + 1) + (gaps (offset + (i + 1))).size)
    (touched : key ∈ keys) : lo + keyRank gaps offset i ∈ keys := by
  have leftEnd := keyRank_before_gap gaps offset (show i < i + 1 by omega)
  have rightEnd := gap_end gaps offset (i + 1)
  have weights := gapWeight_mono gaps offset (show i + 1 + 1 ≤ shape.size + 1 by omega)
  have root : lo + keyRank gaps offset i ∈ Region.keys (withGaps shape gaps offset) lo :=
    (withGaps_keys shape gaps offset lo _).mpr ⟨i, parent, rfl⟩
  apply supernode_gap_required history legal touched
  refine ⟨canonical ▸ root, by omega, ?_, by omega, ?_⟩
  · rw [withGaps_tree_size]
    simp only [keyRank] at rightEnd
    omega
  · intro y below above different member
    rw [← canonical] at member
    obtain ⟨j, _, equal⟩ := (withGaps_keys shape gaps offset lo y).mp member
    by_cases before : j < i
    · have bound := keyRank_strictMono gaps offset before
      have : min (lo + keyRank gaps offset i) key = lo + keyRank gaps offset i := by omega
      rw [this] at below
      omega
    · by_cases same : j = i
      · subst j
        exact different equal
      · have bound := (keyRank_strictMono gaps offset).monotone (show i + 1 ≤ j by omega)
        have : max (lo + keyRank gaps offset i) key = key := by omega
        rw [this] at above
        omega

end RotationBST.Arboral.Online.Supernode
