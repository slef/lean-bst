module

public import RotationBST.Arboral.Online.Split.Finger.Locate.Split.Abstract
public import RotationBST.Arboral.Online.Split.Finger.Locate.Embedding.Proofs
public import RotationBST.Arboral.Online.Split.Finger.Binary.Partition.Open

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

/-- The locally computed rotations expose the requested key in the full input
finger BST, with logarithmic rank cost and no whole-tree conversion. -/
theorem splitLocated_spec {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    Access (binaryView t).tree (splitLocated t rank).1 rank (splitLocated t rank).2 ∧
      (splitLocated t rank).2 ≤ 23 * (Nat.log2 (rank + 1) + 1) + 1 := by
  have balanced := (locate_balance valid rank).1
  have contains := locate_contains t rank existsKey
  have height := locate_height valid rank
  cases rest : contextRemainder (locate t rank).outer with
  | none =>
    have access := fingerSplit_access balanced rank contains
    have cost := fingerSplit_cost balanced rank contains
    constructor
    · rw [locate_view t rank]
      simpa only [enclosingView, splitLocated, rest] using access
    · simp only [splitLocated, rest]
      omega
  | some tail =>
    have access := fingerSplit_open_access balanced rank contains tail
    have cost := fingerSplit_open_cost balanced rank contains
    constructor
    · rw [locate_view t rank]
      simpa only [enclosingView, splitLocated, rest] using access
    · simp only [splitLocated, rest]
      omega

end RotationBST.Arboral.Split.Multiway.Finger
