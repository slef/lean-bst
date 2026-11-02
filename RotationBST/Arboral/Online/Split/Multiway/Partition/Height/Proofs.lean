module

public import RotationBST.Arboral.Online.Split.Multiway.Partition.Height.Composition

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Partition
open Join

/-- Splitting does not increase the lexicographic pair of height and root
occupancy on either side. Root absorption is essential for the full-node case. -/
theorem cutAux_capacity (fuel : Nat) {h : Nat} {t : Multiway} (valid : Balanced h t)
    (enough : t.size < fuel) (rank : Nat) (existsKey : rank < t.size) :
    (cutAux fuel h t rank).Within (4 * h + rootKeys t) := by
  induction fuel generalizing h t rank with
  | zero => omega
  | succ fuel ih =>
    have nonempty : t ≠ .nil := by intro eq; subst t; simp [size] at existsKey
    cases parts : children h t with
    | mk l r =>
      have shape := children_binary h nonempty
      have balanced := children_valid valid
      rw [parts] at shape balanced
      change l.Valid ∧ r.Valid at balanced
      change t.binary = .node l.tree.binary r.tree.binary at shape
      have sizes := congrArg Tree.size shape
      simp only [Tree.size, binary_size] at sizes
      by_cases before : rank < l.tree.size
      · have child := ih balanced.1 (by omega) rank before
        have childBalance := (cutAux_spec fuel balanced.1 (by omega) rank before).1
        have bounded : (cutAux fuel l.height l.tree rank).Within (children h t).1.capacity := by
          simpa only [parts, Piece.capacity] using child
        have result := afterLeft_capacity valid nonempty childBalance bounded
        simpa only [cutAux, parts, before, ite_true] using result
      · by_cases atRoot : rank = l.tree.size
        · have bounds := children_capacity valid
          simpa only [cutAux, parts, atRoot, Nat.lt_irrefl, ite_false, ite_true, Cut.Within] using bounds
        · have nextRank : rank - l.tree.size - 1 < r.tree.size := by omega
          have child := ih balanced.2 (by omega) _ nextRank
          have childBalance := (cutAux_spec fuel balanced.2 (by omega) _ nextRank).1
          have bounded : (cutAux fuel r.height r.tree (rank - l.tree.size - 1)).Within (children h t).2.capacity := by
            simpa only [parts, Piece.capacity] using child
          have result := afterRight_capacity valid nonempty childBalance bounded
          simpa only [cutAux, parts, before, ite_false, atRoot] using result

/-- Neither interval produced by splitting is taller than the input tree. -/
theorem run_height {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    (run h t rank).left.height ≤ h ∧ (run h t rank).right.height ≤ h := by
  have bound := cutAux_capacity (t.size + 1) valid (by omega) rank existsKey
  have keys := rootKeys_bound t
  change (run h t rank).Within (4 * h + rootKeys t) at bound
  simp only [Cut.Within, Piece.capacity] at bound
  omega

end RotationBST.Arboral.Split.Multiway.Partition
