module

public import RotationBST.Structures.SplitTree.Finger.Binary.Conversion.Defs
public import RotationBST.Structures.SplitTree.Finger.Binary.Rotations

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Finger

/-- Each multiway level is rearranged once; the enclosing remainder is unchanged. -/
theorem openConversion_rotations (t : Multiway) (rest : Tree) :
    Rotations (.node t.binary rest) (openView t rest) (openConversionCost t) := by
  induction t generalizing rest with
  | nil => exact .refl
  | two a b ia ib =>
    have child := ia (.node b.binary rest)
    simpa only [binary, openView, binaryView, comb_append, comb, openConversionCost] using
      Rotations.step Rotate.right child
  | three a b c ia ib ic =>
    have child := ia (.node b.binary (.node c.binary rest))
    simpa only [binary, openView, binaryView, comb_append, comb, openConversionCost, Nat.add_assoc] using
      Rotations.step Rotate.right (Rotations.step (Rotate.inRight Rotate.right) child)
  | four a b c d ia ib ic id =>
    have child := ia (.node b.binary (.node c.binary (.node d.binary rest)))
    have start : Rotations (.node (.node (.node a.binary b.binary) (.node c.binary d.binary)) rest)
        (.node a.binary (.node b.binary (.node c.binary (.node d.binary rest)))) 3 :=
      .step .right (.step (.inRight .right) (.step .right .refl))
    have steps := start.append child
    simpa only [binary, openView, binaryView, comb_append, comb, openConversionCost,
      Nat.add_comm 3] using steps

/-- Conversion to the minimum-finger BST takes only a linear number of rotations
in the multiway height, independently of the retained off-path subtree sizes. -/
theorem conversion_rotations (t : Multiway) :
    Rotations t.binary (binaryView t).tree (conversionCost t) := by
  cases t with
  | nil => exact .refl
  | two a b =>
    simpa only [binary, binaryView, BinaryView.tree, comb_append, comb, openView, conversionCost] using
      openConversion_rotations a b.binary
  | three a b c =>
    simpa only [binary, binaryView, BinaryView.tree, comb_append, comb, openView, conversionCost] using
      openConversion_rotations a (.node b.binary c.binary)
  | four a b c d =>
    simpa only [binary, binaryView, BinaryView.tree, comb_append, comb, openView, conversionCost] using
      Rotations.step Rotate.right (openConversion_rotations a (.node b.binary (.node c.binary d.binary)))

theorem openConversion_cost {h : Nat} {t : Multiway} (valid : Balanced h t) :
    openConversionCost t ≤ 3 * h := by
  induction valid <;> simp only [openConversionCost] <;> omega

theorem conversion_cost {h : Nat} {t : Multiway} (valid : Balanced h t) : conversionCost t ≤ 3 * h := by
  cases valid with
  | nil => exact Nat.le_refl _
  | two ha hb => have bound := openConversion_cost ha; simp only [conversionCost]; omega
  | three ha hb hc => have bound := openConversion_cost ha; simp only [conversionCost]; omega
  | four ha hb hc hd => have bound := openConversion_cost ha; simp only [conversionCost]; omega

end RotationBST.Geometric.Split.Multiway.Finger
