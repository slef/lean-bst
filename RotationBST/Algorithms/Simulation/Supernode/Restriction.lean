module

public import RotationBST.Algorithms.Simulation.Supernode.Proofs

@[expose] public section
namespace RotationBST.Arboral

/-- Restricting an interval while retaining one of its maximum-priority keys
preserves the maximum. No tie-breaking order is needed. -/
theorem supernodePriority_restrict {P : Finset Point} {lo hi first last : Nat}
    (lower : lo ≤ first) (upper : last ≤ hi)
    (retained : (supernodeKeys P lo hi ∩ Finset.Ico first last).Nonempty) :
    supernodePriority P first last = supernodePriority P lo hi := by
  obtain ⟨key, member⟩ := retained
  obtain ⟨root, inside⟩ := Finset.mem_inter.mp member
  have priority := (Finset.mem_filter.mp root).2
  apply le_antisymm
  · apply Finset.sup_le
    intro x member
    obtain ⟨xl, xu⟩ := Finset.mem_Ico.mp member
    exact supernode_priority_upper P (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  · rw [← priority]
    exact supernode_priority_upper P inside

/-- A surviving interval of a split supernode has exactly the old root keys
that lie within it, provided at least one root key survives. -/
theorem supernodeKeys_restrict {P : Finset Point} {lo hi first last : Nat}
    (lower : lo ≤ first) (upper : last ≤ hi)
    (retained : (supernodeKeys P lo hi ∩ Finset.Ico first last).Nonempty) :
    supernodeKeys P first last = supernodeKeys P lo hi ∩ Finset.Ico first last := by
  have priority := supernodePriority_restrict lower upper retained
  ext key
  simp only [supernodeKeys, Finset.mem_filter, Finset.mem_inter, priority]
  constructor
  · rintro ⟨inside, equal⟩
    obtain ⟨kl, ku⟩ := Finset.mem_Ico.mp inside
    exact ⟨⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, equal⟩, inside⟩
  · rintro ⟨⟨_, equal⟩, inside⟩
    exact ⟨inside, equal⟩

end RotationBST.Arboral
