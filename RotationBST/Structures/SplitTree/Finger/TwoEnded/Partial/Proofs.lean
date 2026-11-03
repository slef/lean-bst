module

public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Partial.Defs
public import RotationBST.Structures.SplitTree.Finger.TwoEnded.Hierarchy.Proofs

@[expose] public section
namespace RotationBST.SplitTree.Multiway.Finger.TwoEnded

theorem runPlan_spec (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    (runPlan plan input).1.Valid ∧
      Rotations (intervalTree input) (runPlan plan input).1.tree (runPlan plan input).2 := by
  induction plan generalizing input with
  | stop => exact ⟨valid, .refl⟩
  | branch rank l r il ir =>
    cases input with
    | none => exact False.elim applicable
    | some state =>
      have good := split_valid valid rank applicable.1
      have left := il _ good.1 applicable.2.1
      have right := ir _ good.2 applicable.2.2
      have access := split_access valid rank applicable.1
      exact ⟨⟨left.1, right.1⟩, (access.1.append left.2.inLeft).append right.2.inRight⟩

/-- Unspent leaf reserves remain in the bound, ready for later rows. -/
theorem runPlan_credit (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    (runPlan plan input).2 + 14 * (runPlan plan input).1.reserve ≤
      14 * intervalNodes input + 3000 * totalCharge (runPlan plan input).1.tree := by
  induction plan generalizing input with
  | stop => simp [runPlan, Partitioned.reserve]
  | branch rank l r il ir =>
    cases input with
    | none => exact False.elim applicable
    | some state =>
      have good := split_valid valid rank applicable.1
      have parts := split_sizes valid rank applicable.1
      have left := il _ good.1 applicable.2.1
      have right := ir _ good.2 applicable.2.2
      have leftSize := (runPlan_spec l _ good.1 applicable.2.1).2.size_eq
      have rightSize := (runPlan_spec r _ good.2 applicable.2.2).2.size_eq
      have cost := split_credit valid rank applicable.1
      have chargeEq : Nat.log2 (min rank (state.size - 1 - rank) + 1) =
          Nat.log2 (min (runPlan l (split state rank).left).1.tree.size
            (runPlan r (split state rank).right).1.tree.size + 1) := by
        rw [← leftSize, ← rightSize, parts.1, parts.2]
      rw [chargeEq] at cost
      simp only [runPlan, Partitioned.tree, Partitioned.reserve, totalCharge, charge, intervalNodes, Fragment.nodes] at *
      omega

/-- A partial hierarchy is already linearly bounded, without executing any
future splits or discarding the reserves of its retained intervals. -/
theorem runPlan_linear (plan : Plan) (input : Option State) (valid : IntervalValid input)
    (applicable : plan.Applicable input) :
    (runPlan plan input).2 + 14 * (runPlan plan input).1.reserve ≤
      6014 * (intervalTree input).size := by
  have credit := runPlan_credit plan input valid applicable
  have reserve := intervalNodes_le_size input
  have charges := totalCharge_linear (runPlan plan input).1.tree
  have sizes := (runPlan_spec plan input valid applicable).2.size_eq
  omega

end RotationBST.SplitTree.Multiway.Finger.TwoEnded
