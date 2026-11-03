module

public import RotationBST.Algorithms.Simulation.Supernode.Ranks.Defs
public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Regions

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Pointer.Lazy.Skeleton

theorem gapWeight_mono (gaps : Nat → Tree) (offset : Nat) {n m : Nat} (ordered : n ≤ m) :
    gapWeight gaps offset n ≤ gapWeight gaps offset m := by
  obtain ⟨rest, rfl⟩ := Nat.exists_eq_add_of_le ordered
  rw [gapWeight_add]
  omega

theorem keyRank_strictMono (gaps : Nat → Tree) (offset : Nat) : StrictMono (keyRank gaps offset) := by
  intro a b ordered
  have weights := gapWeight_mono gaps offset (show a + 1 ≤ b + 1 by omega)
  simp only [keyRank]
  omega

theorem keyRank_shift (gaps : Nat → Tree) (offset first rank : Nat) :
    keyRank gaps offset (first + rank) =
      first + gapWeight gaps offset first + keyRank gaps (offset + first) rank := by
  simp only [keyRank]
  rw [show first + rank + 1 = first + (rank + 1) by omega, gapWeight_add gaps offset first (rank + 1)]
  omega

/-- The active keys of an embedded supernode are exactly the images of its
key-only ranks; all keys inside gap subtrees are excluded. -/
theorem withGaps_keys (shape : Tree) (gaps : Nat → Tree) (offset lo key : Nat) :
    key ∈ Region.keys (withGaps shape gaps offset) lo ↔
      ∃ rank < shape.size, key = lo + keyRank gaps offset rank := by
  induction shape generalizing offset lo with
  | nil => simp [withGaps, Region.keys, Tree.size]
  | node l r il ir =>
    simp only [withGaps, Region.keys, Finset.mem_insert, Finset.mem_union, il, ir]
    constructor
    · intro member
      rcases member with root | left | right
      · refine ⟨l.size, by simp only [Tree.size]; omega, ?_⟩
        simpa only [withGaps_tree_size, keyRank] using root
      · obtain ⟨rank, bound, equal⟩ := left
        exact ⟨rank, by simp only [Tree.size]; omega, equal⟩
      · obtain ⟨rank, bound, equal⟩ := right
        refine ⟨l.size + 1 + rank, by simp only [Tree.size]; omega, ?_⟩
        rw [keyRank_shift gaps offset (l.size + 1) rank]
        simp only [withGaps_tree_size] at equal
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using equal
    · rintro ⟨rank, bound, equal⟩
      by_cases left : rank < l.size
      · exact Or.inr (Or.inl ⟨rank, left, equal⟩)
      · by_cases root : rank = l.size
        · left
          simpa only [root, keyRank, withGaps_tree_size] using equal
        · right; right
          refine ⟨rank - (l.size + 1), by simp only [Tree.size] at bound; omega, ?_⟩
          have shift := keyRank_shift gaps offset (l.size + 1) (rank - (l.size + 1))
          rw [show l.size + 1 + (rank - (l.size + 1)) = rank by omega] at shift
          rw [shift] at equal
          simp only [withGaps_tree_size]
          simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using equal

/-- Pullback followed by rank expansion is exactly intersection with the
supernode's active keys, including when the row also touches its gaps. -/
theorem touchedRanks_image (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat) (keys : Finset Nat) :
    (touchedRanks shape.size gaps offset lo keys).image (fun rank => lo + keyRank gaps offset rank) =
      keys ∩ Region.keys (withGaps shape gaps offset) lo := by
  ext key
  simp only [Finset.mem_image, touchedRanks, Finset.mem_filter, Finset.mem_range,
    Finset.mem_inter, withGaps_keys]
  constructor
  · rintro ⟨rank, ⟨bound, touched⟩, equal⟩
    exact ⟨equal ▸ touched, rank, bound, equal.symm⟩
  · rintro ⟨touched, rank, bound, equal⟩
    exact ⟨rank, ⟨bound, equal ▸ touched⟩, equal.symm⟩

theorem touchedRanks_card (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat) (keys : Finset Nat) :
    (touchedRanks shape.size gaps offset lo keys).card =
      (keys ∩ Region.keys (withGaps shape gaps offset) lo).card := by
  have injective : Function.Injective (fun rank => lo + keyRank gaps offset rank) := by
    intro a b equal
    dsimp only at equal
    exact (keyRank_strictMono gaps offset).injective (by omega)
  have same := congrArg Finset.card (touchedRanks_image shape gaps offset lo keys)
  rwa [Finset.card_image_of_injective _ injective] at same

theorem touchedRanks_card_le (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat) (keys : Finset Nat) :
    (touchedRanks shape.size gaps offset lo keys).card ≤ keys.card := by
  rw [touchedRanks_card]
  exact Finset.card_le_card Finset.inter_subset_left

end RotationBST.Arboral.Online.Supernode
