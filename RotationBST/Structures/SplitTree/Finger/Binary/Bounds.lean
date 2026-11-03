module

public import RotationBST.Structures.SplitTree.Finger.Binary.Rotations
public import RotationBST.Structures.SplitTree.Multiway.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger

/-- No level of a balanced multiway tree is empty. -/
theorem height_le_size {h : Nat} {t : Multiway} (valid : Balanced h t) : h ≤ t.size := by
  induction valid <;> simp_all only [size] <;> omega

/-- Each multiway level contributes at most three binary spine separators. -/
theorem binaryView_length {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (binaryView t).spine.length ≤ 3 * h := by
  induction valid <;> simp_all only [binaryView, List.length_append, List.length_cons, List.length_nil] <;> omega

/-- The finger comparison tree can be initialized at linear rotation cost.
The off-path balanced siblings pay for the rotations along the growing spine. -/
theorem viewCost_linear {h : Nat} {t : Multiway} (valid : Balanced h t) : viewCost t ≤ 3 * t.size := by
  induction valid with
  | nil => exact Nat.le_refl _
  | two ha hb ia ib =>
    have length := binaryView_length ha
    have sibling := height_le_size hb
    simp only [viewCost, size]
    omega
  | three ha hb hc ia ib ic =>
    have length := binaryView_length ha
    have sibling := height_le_size hb
    simp only [viewCost, size]
    omega
  | four ha hb hc hd ia ib ic id =>
    have length := binaryView_length ha
    have siblingB := height_le_size hb
    have siblingC := height_le_size hc
    simp only [viewCost, size]
    omega

theorem binaryView_size (t : Multiway) : (binaryView t).tree.size = t.size := by
  have equal := (binaryView_rotations t).size_eq
  rw [binary_size] at equal
  exact equal.symm

end RotationBST.SplitTree.Multiway.Finger
