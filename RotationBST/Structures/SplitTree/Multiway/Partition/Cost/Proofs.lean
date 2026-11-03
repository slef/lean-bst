module

public import RotationBST.Structures.SplitTree.Multiway.Partition.Cost.Composition

@[expose] public section
namespace RotationBST.Geometric.Split.Multiway.Partition
open Join
open RotationBST.Tree (depth)

theorem cutAux_cost (fuel : Nat) {h : Nat} {t : Multiway} (valid : Balanced h t)
    (enough : t.size < fuel) (rank : Nat) (existsKey : rank < t.size) :
    (cutAux fuel h t rank).cost ≤
      3 * ((cutAux fuel h t rank).left.height + (cutAux fuel h t rank).right.height) +
        4 * depth t.binary rank := by
  induction fuel generalizing h t rank with
  | zero => omega
  | succ fuel ih =>
    have nonempty : t ≠ .nil := by intro eq; subst t; simp [size] at existsKey
    cases parts : children h t with
    | mk l r =>
      have shape := children_binary h nonempty
      have balanced := children_valid valid
      have gaps := children_height_gap valid
      rw [parts] at shape balanced gaps
      change l.Valid ∧ r.Valid at balanced
      change t.binary = .node l.tree.binary r.tree.binary at shape
      change l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1 at gaps
      have sizes := congrArg Tree.size shape
      simp only [Tree.size, binary_size] at sizes
      by_cases before : rank < l.tree.size
      · have child := ih balanced.1 (by omega) rank before
        have childBalance := (cutAux_spec fuel balanced.1 (by omega) rank before).1
        have capacities := cutAux_capacity fuel balanced.1 (by omega) rank before
        have keys := rootKeys_bound l.tree
        simp only [Cut.Within, Piece.capacity] at capacities
        have gap : (cutAux fuel l.height l.tree rank).right.height ≤ r.height + 1 := by omega
        have result := afterLeft_cost childBalance balanced.2 gap child
        simpa only [cutAux, parts, before, ite_true, shape, depth, binary_size] using result
      · by_cases atRoot : rank = l.tree.size
        · simp only [cutAux, parts, atRoot, Nat.lt_irrefl, ite_false, ite_true]
          exact Nat.zero_le _
        · have nextRank : rank - l.tree.size - 1 < r.tree.size := by omega
          have child := ih balanced.2 (by omega) _ nextRank
          have childBalance := (cutAux_spec fuel balanced.2 (by omega) _ nextRank).1
          have capacities := cutAux_capacity fuel balanced.2 (by omega) _ nextRank
          have keys := rootKeys_bound r.tree
          simp only [Cut.Within, Piece.capacity] at capacities
          have gap : (cutAux fuel r.height r.tree (rank - l.tree.size - 1)).left.height ≤ l.height + 1 := by omega
          have result := afterRight_cost balanced.1 childBalance gap child
          simpa only [cutAux, parts, before, ite_false, atRoot, shape, depth, binary_size] using result

/-- Root-based splitting takes at most fourteen rotations per multiway level.
This is the rebuilding bound, not yet the smaller-side finger split bound. -/
theorem run_cost {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) : (run h t rank).cost ≤ 14 * h := by
  have cost := cutAux_cost (t.size + 1) valid (by omega) rank existsKey
  have heights := run_height valid rank existsKey
  have path := Finger.binary_depth valid rank
  change (run h t rank).cost ≤ 3 * ((run h t rank).left.height + (run h t rank).right.height) +
    4 * depth t.binary rank at cost
  omega

end RotationBST.Geometric.Split.Multiway.Partition
