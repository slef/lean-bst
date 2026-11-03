module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.StaticOptimality.AbstractBridge

@[expose] public section

/-! `Bounds/Abstract` defines frequency entropy and the quantified property.
The first result permits unused keys. The second is the paper's sharper result
under its explicit hypothesis that every stored key occurs. -/
namespace RotationBST.Splay.Results

theorem staticOptimality : HasStaticOptimalityBound algorithm :=
  Splay.hasWorkingSetBound.staticOptimality algorithm

theorem staticOptimality_all_accessed (t : Tree) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 4 * Bounds.staticCost t.size xs :=
  Splay.staticOptimality_all_accessed t xs valid covers

/-- The paper's comparison-tree formulation, with no startup when every key occurs. -/
theorem staticOptimality_fixedTree (t u : Tree) (xs : List Nat) (same : t.size = u.size)
    (valid : ∀ x ∈ xs, x < t.size) (covers : ∀ x < t.size, x ∈ xs) :
    (algorithm.totalCost t xs : ℝ) ≤ 12 * (StaticTree.cost u xs : ℝ) :=
  Bridge.staticOptimality_fixedTree t u xs same valid covers

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Splay.Results`: 3 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
