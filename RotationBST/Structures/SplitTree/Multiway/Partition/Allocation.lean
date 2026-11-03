module

public import RotationBST.Structures.SplitTree.Multiway.Partition.Cost.Proofs
public import RotationBST.Structures.SplitTree.Multiway.Join.Allocation

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Partition

theorem children_nodes (h : Nat) (t : Multiway) :
    (children h t).1.tree.nodes + (children h t).2.tree.nodes ≤ t.nodes + 1 := by
  cases t <;> simp only [children, nodes] <;> omega

/-- Node allocation by local splitting is bounded by its certified rotation
count, so later context repairs cannot spend an uncharged node reserve. -/
theorem cutAux_allocation (fuel : Nat) (h : Nat) (t : Multiway) (rank : Nat)
    (enough : t.size < fuel) (existsKey : rank < t.size) :
    (cutAux fuel h t rank).left.tree.nodes + (cutAux fuel h t rank).right.tree.nodes ≤
      t.nodes + 2 * (cutAux fuel h t rank).cost + 1 := by
  induction fuel generalizing h t rank with
  | zero => omega
  | succ fuel ih =>
    have nonempty : t ≠ .nil := by intro eq; subst t; simp [size] at existsKey
    cases parts : children h t with
    | mk l r =>
      have shape := children_binary h nonempty
      have allocated := children_nodes h t
      rw [parts] at shape allocated
      change t.binary = .node l.tree.binary r.tree.binary at shape
      change l.tree.nodes + r.tree.nodes ≤ t.nodes + 1 at allocated
      have sizes := congrArg Tree.size shape
      simp only [Tree.size, binary_size] at sizes
      by_cases before : rank < l.tree.size
      · have child := ih l.height l.tree rank (by omega) before
        have joined := Multiway.Join.compact_allocation (cutAux fuel l.height l.tree rank).right.height
          r.height (cutAux fuel l.height l.tree rank).right.tree r.tree
        simp only [cutAux, parts, before, ite_true, afterLeft]
        omega
      · by_cases atRoot : rank = l.tree.size
        · simpa only [cutAux, parts, atRoot, Nat.lt_irrefl, ite_false, ite_true, Nat.mul_zero, Nat.add_zero] using allocated
        · have nextRank : rank - l.tree.size - 1 < r.tree.size := by omega
          have child := ih r.height r.tree _ (by omega) nextRank
          have joined := Multiway.Join.compact_allocation l.height
            (cutAux fuel r.height r.tree (rank - l.tree.size - 1)).left.height l.tree
            (cutAux fuel r.height r.tree (rank - l.tree.size - 1)).left.tree
          simp only [cutAux, parts, before, ite_false, atRoot, afterRight]
          omega

theorem run_allocation (h : Nat) (t : Multiway) (rank : Nat) (existsKey : rank < t.size) :
    (run h t rank).left.tree.nodes + (run h t rank).right.tree.nodes ≤
      t.nodes + 2 * (run h t rank).cost + 1 :=
  cutAux_allocation _ h t rank (by omega) existsKey

end RotationBST.Geometric.Split.Multiway.Partition
