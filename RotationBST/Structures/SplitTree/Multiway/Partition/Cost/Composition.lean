module

public import RotationBST.Structures.SplitTree.Multiway.Partition.Height.Proofs
public import RotationBST.Structures.SplitTree.Finger.Binary.Search.Basic

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Partition
open Join

theorem children_height_gap {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (children h t).1.height ≤ (children h t).2.height + 1 ∧
      (children h t).2.height ≤ (children h t).1.height + 1 := by
  cases valid <;> simp [children]; omega

/-- The cost of joining a partial interval can be charged to its height increase,
with a constant allowance when it is one level taller than the sibling. -/
theorem afterLeft_cost {cut : Cut} {right : Piece} {depth : Nat}
    (balanced : cut.Valid) (sibling : right.Valid)
    (gap : cut.right.height ≤ right.height + 1)
    (bound : cut.cost ≤ 3 * (cut.left.height + cut.right.height) + 4 * depth) :
    (afterLeft cut right).cost ≤
      3 * ((afterLeft cut right).left.height + (afterLeft cut right).right.height) + 4 * (depth + 1) := by
  have cost := compact_cost cut.right.height right.height cut.right.tree right.tree
  have heights := (compact_balance balanced.2 sibling).2
  simp only [afterLeft]
  omega

theorem afterRight_cost {left : Piece} {cut : Cut} {depth : Nat}
    (sibling : left.Valid) (balanced : cut.Valid)
    (gap : cut.left.height ≤ left.height + 1)
    (bound : cut.cost ≤ 3 * (cut.left.height + cut.right.height) + 4 * depth) :
    (afterRight left cut).cost ≤
      3 * ((afterRight left cut).left.height + (afterRight left cut).right.height) + 4 * (depth + 1) := by
  have cost := compact_cost left.height cut.left.height left.tree cut.left.tree
  have heights := (compact_balance sibling balanced.1).2
  simp only [afterRight]
  omega

end RotationBST.SplitTree.Multiway.Partition
