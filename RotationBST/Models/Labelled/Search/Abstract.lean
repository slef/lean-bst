module

import RotationBST.Audit.Check
public import RotationBST.Models.Labelled.Search.AbstractBridge

@[expose] public section
namespace RotationBST.LabelledTree.Search.Results

/-- Sparse labels preserve shape and exactly the supplied inorder key list. -/
theorem labelling (t : Tree) (keys : List Nat) (same : keys.length = t.size) :
    (t.labelWith keys).erase = t ∧ (t.labelWith keys).inorder = keys :=
  ⟨Tree.labelWith_erase t keys, Tree.labelWith_inorder t keys same⟩

theorem ordered (t : Tree) (keys : List Nat) (same : keys.length = t.size)
    (increasing : keys.Pairwise (· < ·)) : (t.labelWith keys).Ordered :=
  Tree.labelWith_ordered t keys same increasing

theorem execution (t : LabelledTree Nat) (x : Nat) :
    Search t x (lookup t x).1 (lookup t x).2 := lookup_search t x

theorem membership (t : LabelledTree Nat) (ordered : t.Ordered) (x : Nat) :
    (lookup t x).1 = true ↔ x ∈ t.inorder := lookup_correct t ordered x

/-- Actual key comparisons have precisely the ordinary rank-depth hit cost. -/
theorem hit_cost (t : Tree) (keys : List Nat) (same : keys.length = t.size)
    (increasing : keys.Pairwise (· < ·)) (i : Nat) (valid : i < keys.length) :
    (lookup (t.labelWith keys) keys[i]).2 = Tree.depth t i + 1 :=
  lookup_rank_cost t keys same increasing i valid

/-- The depth bound applies to unsuccessful searches too. -/
theorem uniform_cost (t : LabelledTree Nat) (x : Nat) (D : ℝ) (nonnegative : 0 ≤ D)
    (depths : ∀ i < t.erase.size, (Tree.depth t.erase i : ℝ) ≤ D) :
    ((lookup t x).2 : ℝ) ≤ D + 1 := lookup_cost_le t x D nonnegative depths

end RotationBST.LabelledTree.Search.Results

/-- info: abstract audit passed for `RotationBST.LabelledTree.Search.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.LabelledTree.Search.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Models.Labelled.Search.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract]
