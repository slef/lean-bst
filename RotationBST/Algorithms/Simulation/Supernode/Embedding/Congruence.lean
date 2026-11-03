module

public import RotationBST.Algorithms.Simulation.Supernode.Embedding.Proofs

@[expose] public section
namespace RotationBST.Geometric.Online.Supernode

/-- An embedding depends only on the gaps used by its key shape. Offsets may
change when a consecutive run is stored as an independent supernode. -/
theorem withGaps_congr (shape : Tree) (gaps other : Nat → Tree) (offset start : Nat)
    (same : ∀ i, i ≤ shape.size → gaps (offset + i) = other (start + i)) :
    withGaps shape gaps offset = withGaps shape other start := by
  induction shape generalizing offset start with
  | nil => simpa only [withGaps, Nat.add_zero] using congrArg Pointer.Lazy.Skeleton.hole (same 0 (by simp))
  | node l r il ir =>
    simp only [withGaps]
    congr 1
    · apply il
      intro i bound
      exact same i (by simp only [Tree.size]; omega)
    · apply ir
      intro i bound
      have equal := same (l.size + 1 + i) (by simp only [Tree.size]; omega)
      simpa only [Nat.add_assoc] using equal

/-- The accumulated gap size also depends only on the traversed prefix. -/
theorem gapWeight_congr (gaps other : Nat → Tree) (offset start count : Nat)
    (same : ∀ i, i < count → gaps (offset + i) = other (start + i)) :
    gapWeight gaps offset count = gapWeight other start count := by
  induction count generalizing offset start with
  | zero => rfl
  | succ count ih =>
    simp only [gapWeight]
    have first := same 0 (by omega)
    simp only [Nat.add_zero] at first
    rw [first, ih]
    intro i bound
    have equal := same (1 + i) (by omega)
    simpa only [Nat.add_assoc] using equal

end RotationBST.Geometric.Online.Supernode
