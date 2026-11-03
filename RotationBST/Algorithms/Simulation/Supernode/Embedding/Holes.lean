module

public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Regions

@[expose] public section
namespace RotationBST.Arboral.Online.Supernode
open Pointer.Lazy.Skeleton

/-- Every retained gap has its original ordinal and the exact absolute offset
obtained by counting preceding supernode keys and preceding gap sizes. -/
theorem withGaps_hole (shape : Tree) (gaps : Nat → Tree) (offset lo : Nat)
    {hole : Nat × Tree} (member : hole ∈ Region.holes (withGaps shape gaps offset) lo) :
    ∃ i ≤ shape.size,
      hole = (lo + i + gapWeight gaps offset i, gaps (offset + i)) := by
  induction shape generalizing offset lo with
  | nil =>
    have equal : hole = (lo, gaps offset) := List.mem_singleton.mp member
    refine ⟨0, by simp [Tree.size], ?_⟩
    simpa only [Nat.add_zero, gapWeight] using equal
  | node l r il ir =>
    simp only [withGaps, Region.holes] at member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨i, bound, equal⟩ := il _ _ member
      exact ⟨i, by simp only [Tree.size]; omega, equal⟩
    · obtain ⟨i, bound, equal⟩ := ir _ _ member
      refine ⟨l.size + 1 + i, by simp only [Tree.size]; omega, ?_⟩
      rw [gapWeight_add gaps offset (l.size + 1) i]
      simp only [withGaps_tree_size] at equal
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using equal

/-- Every external gap ordinal occurs in the realized region. -/
theorem withGaps_hole_mem (shape : Tree) (gaps : Nat → Tree) (offset lo i : Nat)
    (bound : i ≤ shape.size) :
    (lo + i + gapWeight gaps offset i, gaps (offset + i)) ∈
      Region.holes (withGaps shape gaps offset) lo := by
  induction shape generalizing offset lo i with
  | nil =>
    have zero : i = 0 := by simp only [Tree.size] at bound; omega
    simp [zero, withGaps, Region.holes, gapWeight]
  | node l r il ir =>
    simp only [withGaps, Region.holes, List.mem_append]
    by_cases before : i ≤ l.size
    · exact Or.inl (il offset lo i before)
    · have inside : i - (l.size + 1) ≤ r.size := by simp only [Tree.size] at bound; omega
      have child := ir (offset + l.size + 1)
        (lo + (withGaps l gaps offset).tree.size + 1) (i - (l.size + 1)) inside
      have index : l.size + 1 + (i - (l.size + 1)) = i := by omega
      have weights := gapWeight_add gaps offset (l.size + 1) (i - (l.size + 1))
      rw [index] at weights
      right
      rw [weights]
      simp only [withGaps_tree_size] at child
      have offsetEq : offset + l.size + 1 + (i - (l.size + 1)) = offset + i := by omega
      rw [offsetEq] at child
      simp only [withGaps_tree_size, Nat.add_assoc] at child ⊢
      convert child using 1; congr 1; omega

end RotationBST.Arboral.Online.Supernode
