module

public import RotationBST.Arboral.Online.Split.Finger.Binary.Search.Rank
public import RotationBST.Bounds.StaticTree.Comparison

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- A concrete splay accesses any key of the initialized minimum finger within
the logarithmic rank-distance bound. This does not assert that splaying retains
the finger representation needed by subsequent splits. -/
theorem binaryView_access {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (Splay.run (binaryView t).tree rank).1 rank
        (Splay.run (binaryView t).tree rank).2 ∧
      (Splay.run (binaryView t).tree rank).2 ≤ 5 * Nat.log2 (rank + 1) + 6 := by
  have within : rank < (binaryView t).tree.size := by rwa [binaryView_size]
  refine ⟨(Splay.run_correct _ rank within).1, ?_⟩
  have rotations : (Splay.run (binaryView t).tree rank).2 ≤ StaticTree.depth (binaryView t).tree rank := by
    rw [← StaticTree.locate_depth]
    unfold Splay.run
    cases focus : (Splay.locate (binaryView t).tree rank).focus <;> simp [focus]
  exact Nat.le_trans rotations (binaryView_depth valid rank existsKey)

end RotationBST.Arboral.Split.Multiway.Finger
