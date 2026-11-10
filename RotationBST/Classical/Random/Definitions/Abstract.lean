module

public import RotationBST.Models.Rotation.Abstract

@[expose] public section

/-! Binary search trees built by insertion without rebalancing. Keys are
labels compared on insertion; the shape is the `erase`. -/
namespace RotationBST.Classical.Random

/-- Insert key `y` as a new leaf, going left at larger keys and right otherwise. -/
def insertKey : LabelledTree Nat → Nat → LabelledTree Nat
  | .nil, y => .node .nil y .nil
  | .node l x r, y => if y < x then .node (insertKey l y) x r else .node l x (insertKey r y)

/-- Insert the keys of `order` one after the other, starting from the empty tree. -/
def insertAll (order : List Nat) : LabelledTree Nat := order.foldl insertKey .nil

end RotationBST.Classical.Random
