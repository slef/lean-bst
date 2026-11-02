module

import RotationBST.AbstractAudit.Check
public import RotationBST.Bounds.StaticTree.AbstractBridge

@[expose] public section

/-! Static optimality as comparison with an actual fixed search tree.
`Definitions/Abstract` gives ordinary search depth and its summed pointer cost.
The prefix-code inequality connects this meaning to frequency entropy. -/
namespace RotationBST.StaticTree.Results

theorem entropy_lower_bound (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    Bounds.staticCost t.size xs ≤ 3 * (StaticTree.cost t xs : ℝ) :=
  entropy_le_cost t xs valid

/-- This benchmark is exactly realized by searches that never rotate the tree. -/
theorem pointer_execution (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    Pointer.Execution t xs t (StaticTree.cost t xs) :=
  execution t xs valid

/-- Every algorithm with a working-set bound competes with every fixed BST on
the same ordered key universe, up to uniform constants and initialization. -/
theorem workingSet_competes (a : Algorithm) (workingSet : HasWorkingSetBound a) :
    ∃ C D : Nat, ∀ t u xs, t.size = u.size → (∀ x ∈ xs, x < t.size) →
      (a.totalCost t xs : ℝ) ≤ (C : ℝ) * StaticTree.cost u xs +
        (D : ℝ) * t.size * (1 + (t.size.log2 : ℝ)) :=
  (workingSet.staticOptimality a).fixedTree a

end RotationBST.StaticTree.Results

#check_bst_abstract RotationBST.StaticTree.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Online.Abstract, RotationBST.WorkingSet.Abstract,
  RotationBST.Bounds.Abstract, RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Pointer.Machine.Abstract]
