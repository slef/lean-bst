module

public import RotationBST.Structures.SplitTree.Finger.Binary.Maximum.Defs
public import RotationBST.Structures.SplitTree.Multiway.Proofs

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Finger

theorem leftComb_append (xs ys : List Tree) (tail : Tree) :
    leftComb (xs ++ ys) tail = leftComb xs (leftComb ys tail) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append, leftComb, ih]

theorem maximumOpen_rotations (t : Multiway) (rest : Tree) :
    Rotations (.node rest t.binary) (maximumOpenView t rest) (maximumOpenCost t) := by
  induction t generalizing rest with
  | nil => exact .refl
  | two a b ia ib =>
    simpa only [binary, maximumOpenView, maximumView, leftComb_append, leftComb, maximumOpenCost] using
      Rotations.step Rotate.left (ib (.node rest a.binary))
  | three a b c ia ib ic =>
    simpa only [binary, maximumOpenView, maximumView, leftComb_append, leftComb, maximumOpenCost, Nat.add_assoc] using
      Rotations.step Rotate.left (Rotations.step Rotate.left (ic (.node (.node rest a.binary) b.binary)))
  | four a b c d ia ib ic id =>
    have start : Rotations (.node rest (.node (.node a.binary b.binary) (.node c.binary d.binary)))
        (.node (.node (.node (.node rest a.binary) b.binary) c.binary) d.binary) 3 :=
      .step .left (.step .left (.step (.inLeft (.inLeft .left)) .refl))
    have steps := start.append (id (.node (.node (.node rest a.binary) b.binary) c.binary))
    simpa only [binary, maximumOpenView, maximumView, leftComb_append, leftComb, maximumOpenCost,
      Nat.add_comm 3] using steps

theorem maximum_rotations (t : Multiway) :
    Rotations t.binary (maximumView t).tree (maximumCost t) := by
  cases t with
  | nil => exact .refl
  | two a b =>
    simpa only [binary, maximumView, MaximumView.tree, maximumOpenView, leftComb_append, leftComb, maximumCost] using
      maximumOpen_rotations b a.binary
  | three a b c =>
    simpa only [binary, maximumView, MaximumView.tree, maximumOpenView, leftComb_append, leftComb, maximumCost] using
      Rotations.step Rotate.left (maximumOpen_rotations c (.node a.binary b.binary))
  | four a b c d =>
    simpa only [binary, maximumView, MaximumView.tree, maximumOpenView, leftComb_append, leftComb, maximumCost] using
      Rotations.step Rotate.left (maximumOpen_rotations d (.node (.node a.binary b.binary) c.binary))

theorem maximumOpen_cost {h : Nat} {t : Multiway} (valid : Balanced h t) : maximumOpenCost t ≤ 3 * h := by
  induction valid <;> simp only [maximumOpenCost] <;> omega

theorem maximum_cost {h : Nat} {t : Multiway} (valid : Balanced h t) : maximumCost t ≤ 3 * h := by
  cases valid with
  | nil => exact Nat.le_refl _
  | two ha hb => have bound := maximumOpen_cost hb; simp only [maximumCost]; omega
  | three ha hb hc => have bound := maximumOpen_cost hc; simp only [maximumCost]; omega
  | four ha hb hc hd => have bound := maximumOpen_cost hd; simp only [maximumCost]; omega

theorem maximumView_size (t : Multiway) : (maximumView t).tree.size = t.size := by
  have sizes := (maximum_rotations t).size_eq
  simpa only [binary_size] using sizes.symm

end RotationBST.Arboral.Split.Multiway.Finger
