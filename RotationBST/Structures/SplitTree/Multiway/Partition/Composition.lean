module

public import RotationBST.Structures.SplitTree.Multiway.Partition.Defs
public import RotationBST.Structures.SplitTree.Multiway.Join.Compact.Proofs

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Partition

theorem children_binary (h : Nat) {t : Multiway} (nonempty : t ≠ .nil) :
    t.binary = .node (children h t).1.tree.binary (children h t).2.tree.binary := by
  cases t <;> simp_all [children, binary]

theorem children_valid {h : Nat} {t : Multiway} (valid : Balanced h t) :
    (children h t).1.Valid ∧ (children h t).2.Valid := by
  cases valid with
  | nil => exact ⟨.nil, .nil⟩
  | two ha hb => exact ⟨ha, hb⟩
  | three ha hb hc => exact ⟨ha, .two hb hc⟩
  | four ha hb hc hd => exact ⟨.two ha hb, .two hc hd⟩

theorem afterLeft_valid {cut : Cut} {right : Piece} (valid : cut.Valid) (sibling : right.Valid) :
    (afterLeft cut right).Valid :=
  ⟨valid.1, (Join.compact_balance valid.2 sibling).1⟩

theorem afterRight_valid {left : Piece} {cut : Cut} (sibling : left.Valid) (valid : cut.Valid) :
    (afterRight left cut).Valid :=
  ⟨(Join.compact_balance sibling valid.1).1, valid.2⟩

theorem afterLeft_access {source : Tree} {cut : Cut} {rank : Nat}
    (access : Access source cut.binary rank cut.cost) (right : Piece) :
    Access (.node source right.tree.binary) (afterLeft cut right).binary rank (afterLeft cut right).cost := by
  constructor
  · have expose := access.1.inLeft (r := right.tree.binary)
    have step : Rotations (.node cut.binary right.tree.binary)
        (.node cut.left.tree.binary (.node cut.right.tree.binary right.tree.binary)) 1 := .step .right .refl
    have joined := (Join.compact_rotations cut.right.height right.height cut.right.tree right.tree).inRight
      (l := cut.left.tree.binary)
    exact (expose.append step).append joined
  · exact access.2

theorem afterRight_access {source : Tree} {cut : Cut} {rank : Nat}
    (access : Access source cut.binary rank cut.cost) (left : Piece) :
    Access (.node left.tree.binary source) (afterRight left cut).binary
      (left.tree.size + 1 + rank) (afterRight left cut).cost := by
  constructor
  · have expose := access.1.inRight (l := left.tree.binary)
    have step : Rotations (.node left.tree.binary cut.binary)
        (.node (.node left.tree.binary cut.left.tree.binary) cut.right.tree.binary) 1 := .step .left .refl
    have joined := (Join.compact_rotations left.height cut.left.height left.tree cut.left.tree).inLeft
      (r := cut.right.tree.binary)
    exact (expose.append step).append joined
  · have root := access.2
    change cut.left.tree.binary.size = rank at root
    change (Join.compact left.height cut.left.height left.tree cut.left.tree).tree.binary.size = _
    rw [binary_size, Join.compact_size, ← binary_size cut.left.tree, root]

end RotationBST.Geometric.Split.Multiway.Partition
