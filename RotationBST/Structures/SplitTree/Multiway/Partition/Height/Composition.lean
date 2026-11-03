module

public import RotationBST.Structures.SplitTree.Multiway.Partition.Proofs
public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Capacity

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Partition
open Join

/-- Lexicographic height and root occupancy, encoded as one natural number. -/
def Piece.capacity (piece : Piece) : Nat := 4 * piece.height + rootKeys piece.tree

def Cut.Within (cut : Cut) (capacity : Nat) : Prop :=
  cut.left.capacity ≤ capacity ∧ cut.right.capacity ≤ capacity

theorem children_capacity {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (children h t).1.capacity ≤ 4 * h + rootKeys t ∧
      (children h t).2.capacity ≤ 4 * h + rootKeys t := by
  cases valid with
  | nil => simp [children, Piece.capacity, rootKeys]
  | @two k a b ha hb =>
    have ka := rootKeys_bound a
    have kb := rootKeys_bound b
    simp only [children, Piece.capacity, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @three k a b c ha hb hc =>
    have ka := rootKeys_bound a
    simp only [children, Piece.capacity, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @four k a b c d ha hb hc hd =>
    simp only [children, Piece.capacity, rootKeys]
    try simp only [rootKeys] at *
    omega

theorem afterLeft_capacity {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil)
    {cut : Cut} (balanced : cut.Valid) (bound : cut.Within (children h t).1.capacity) :
    (afterLeft cut (children h t).2).Within (4 * h + rootKeys t) := by
  cases valid with
  | nil => contradiction
  | @two k a b ha hb =>
    have ka := rootKeys_bound a
    simp only [Cut.Within, Piece.capacity, children, Nat.add_sub_cancel] at bound
    have joined := compact_below (h := k + 1) balanced.2 hb (by omega) (by omega)
    simp only [Cut.Within, Piece.capacity, afterLeft, children, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @three k a b c ha hb hc =>
    have ka := rootKeys_bound a
    simp only [Cut.Within, Piece.capacity, children, Nat.add_sub_cancel] at bound
    have smaller : cut.right.height < k + 1 := by omega
    obtain ⟨height, keys⟩ := compact_taller_two_right smaller cut.right.tree b c
    simp only [Cut.Within, Piece.capacity, afterLeft, children, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @four k a b c d ha hb hc hd =>
    simp only [Cut.Within, Piece.capacity, children, rootKeys] at bound
    have joined := compact_with_two_right balanced.2 (.two hc hd) bound.2
    simp only [Cut.Within, Piece.capacity, afterLeft, children, rootKeys]
    try simp only [rootKeys] at *
    omega

theorem afterRight_capacity {h : Nat} {t : Multiway} (valid : Balanced h t) (nonempty : t ≠ .nil)
    {cut : Cut} (balanced : cut.Valid) (bound : cut.Within (children h t).2.capacity) :
    (afterRight (children h t).1 cut).Within (4 * h + rootKeys t) := by
  cases valid with
  | nil => contradiction
  | @two k a b ha hb =>
    have kb := rootKeys_bound b
    simp only [Cut.Within, Piece.capacity, children, Nat.add_sub_cancel] at bound
    have joined := compact_below (h := k + 1) ha balanced.1 (by omega) (by omega)
    simp only [Cut.Within, Piece.capacity, afterRight, children, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @three k a b c ha hb hc =>
    simp only [Cut.Within, Piece.capacity, children, rootKeys] at bound
    have joined := compact_below_minimal_right ha balanced.1 (show k < k + 1 by omega) bound.1
    simp only [Cut.Within, Piece.capacity, afterRight, children, rootKeys, Nat.add_sub_cancel]
    try simp only [rootKeys] at *
    omega
  | @four k a b c d ha hb hc hd =>
    simp only [Cut.Within, Piece.capacity, children, rootKeys] at bound
    have joined := compact_with_two_left (.two ha hb) balanced.1 bound.1
    simp only [Cut.Within, Piece.capacity, afterRight, children, rootKeys]
    try simp only [rootKeys] at *
    omega

end RotationBST.Arboral.Split.Multiway.Partition
