module

public import RotationBST.Arboral.Online.Split.Multiway.Partition.Composition

@[expose] public section
namespace RotationBST.Arboral.Split.Multiway.Partition

/-- Every recursive split exposes the requested rank and retains two balanced
multiway outputs. The counter is the exact number of binary rotations. -/
theorem cutAux_spec (fuel : Nat) {h : Nat} {t : Multiway} (valid : Balanced h t)
    (enough : t.size < fuel) (rank : Nat) (existsKey : rank < t.size) :
    (cutAux fuel h t rank).Valid ∧
      Access t.binary (cutAux fuel h t rank).binary rank (cutAux fuel h t rank).cost := by
  induction fuel generalizing h t rank with
  | zero => omega
  | succ fuel ih =>
    have nonempty : t ≠ .nil := by intro eq; subst t; simp [size] at existsKey
    -- Name the decomposition equation explicitly to reduce the executable branch.
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
        simp only [cutAux, parts, before, ite_true]
        rw [shape]
        exact ⟨afterLeft_valid child.1 balanced.2, afterLeft_access child.2 r⟩
      · by_cases atRoot : rank = l.tree.size
        · simp only [cutAux, parts, atRoot, Nat.lt_irrefl, ite_false, ite_true]
          refine ⟨balanced, ?_⟩
          constructor
          · rw [shape]; exact .refl
          · exact binary_size l.tree
        · have nextRank : rank - l.tree.size - 1 < r.tree.size := by omega
          have child := ih balanced.2 (by omega) _ nextRank
          simp only [cutAux, parts, before, ite_false, atRoot]
          rw [shape]
          have step := afterRight_access child.2 l
          have rankEq : l.tree.size + 1 + (rank - l.tree.size - 1) = rank := by omega
          rw [rankEq] at step
          exact ⟨afterRight_valid balanced.1 child.1, step⟩

theorem run_spec {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    (run h t rank).Valid ∧ Access t.binary (run h t rank).binary rank (run h t rank).cost :=
  cutAux_spec _ valid (by omega) rank existsKey

theorem run_sizes {h : Nat} {t : Multiway} (valid : Balanced h t)
    (rank : Nat) (existsKey : rank < t.size) :
    (run h t rank).left.tree.size = rank ∧ (run h t rank).right.tree.size = t.size - rank - 1 := by
  have access := (run_spec valid rank existsKey).2
  have left := access.2
  change (run h t rank).left.tree.binary.size = rank at left
  rw [binary_size] at left
  have sizes := access.1.size_eq
  simp only [Cut.binary, Tree.size, binary_size] at sizes
  exact ⟨left, by omega⟩

end RotationBST.Arboral.Split.Multiway.Partition
