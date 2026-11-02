module

public import RotationBST.Arboral.Online.LastTouch.Supernode.Proofs

@[expose] public section
namespace RotationBST.Arboral

/-- A key outside the root supernode has a nearest root key with no other
root key between them. This also covers the two exterior gaps. -/
theorem supernode_nearest_gap {P : Finset Point} {lo hi key : Nat}
    (lower : lo ≤ key) (upper : key < hi) (outside : key ∉ supernodeKeys P lo hi) :
    ∃ boundary, SupernodeGap P lo hi boundary key := by
  obtain ⟨boundary, member, nearest⟩ := (supernodeKeys P lo hi).exists_min_image
    (fun root => (root - key) + (key - root)) (supernodeKeys_nonempty P (by omega))
  refine ⟨boundary, member, lower, upper, ?_, ?_⟩
  · intro equal
    exact outside (equal ▸ member)
  · intro y below above different root
    have distance := nearest y root
    omega

/-- Every legal row entering a nonempty interval touches its root supernode.
Thus recursive extraction cannot descend without exposing a parent key. -/
theorem supernode_touched {n time request lo hi : Nat} {P : Finset Point} {keys : Finset Nat}
    (history : History n time P) (legal : Completion n time request P keys)
    (entered : (keys ∩ Finset.Ico lo hi).Nonempty) :
    (keys ∩ supernodeKeys P lo hi).Nonempty := by
  obtain ⟨key, member⟩ := entered
  obtain ⟨touched, inside⟩ := Finset.mem_inter.mp member
  by_cases root : key ∈ supernodeKeys P lo hi
  · exact ⟨key, Finset.mem_inter.mpr ⟨touched, root⟩⟩
  · obtain ⟨boundary, gap⟩ := supernode_nearest_gap
      (Finset.mem_Ico.mp inside).1 (Finset.mem_Ico.mp inside).2 root
    exact ⟨boundary, Finset.mem_inter.mpr ⟨supernode_gap_required history legal touched gap, gap.1⟩⟩

end RotationBST.Arboral
