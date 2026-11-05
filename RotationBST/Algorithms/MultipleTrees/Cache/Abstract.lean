module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.MultipleTrees.Cache.AbstractBridge

@[expose] public section
namespace RotationBST.MultipleTrees.Cache.Results

theorem size (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).erase.size = min capacity n := cacheTree_size n capacity frequency

theorem keys (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).inorder = cacheKeys n capacity frequency ∧
      (cacheKeys n capacity frequency).Perm (selected n capacity frequency) :=
  ⟨cacheTree_inorder n capacity frequency, cacheKeys_perm n capacity frequency⟩

theorem ordered (n capacity : Nat) (frequency : Nat → Nat) :
    (cacheTree n capacity frequency).Ordered := cacheTree_ordered n capacity frequency

theorem membership (n capacity : Nat) (frequency : Nat → Nat) (x : Nat) :
    (LabelledTree.lookup (cacheTree n capacity frequency) x).1 = true ↔
      x ∈ selected n capacity frequency := cacheTree_lookup n capacity frequency x

theorem uniform (n capacity : Nat) (frequency : Nat → Nat) (x : Nat)
    (nonempty : 0 < min capacity n) :
    ((LabelledTree.lookup (cacheTree n capacity frequency) x).2 : ℝ) ≤
      Real.logb 2 (2 * ((min capacity n : Nat) : ℝ)) + 1 := cacheTree_uniform n capacity frequency x nonempty

theorem weighted (n capacity : Nat) (frequency : Nat → Nat) (x : Nat)
    (stored : x ∈ selected n capacity frequency) (positive : 0 < frequency x) :
    ((LabelledTree.lookup (cacheTree n capacity frequency) x).2 : ℝ) ≤
      Real.logb 2 (3 * (((List.range n).map frequency).sum : ℝ) / frequency x) + 1 :=
  cacheTree_weighted n capacity frequency x stored positive

end RotationBST.MultipleTrees.Cache.Results

/-- info: abstract audit passed for `RotationBST.MultipleTrees.Cache.Results`: 6 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.MultipleTrees.Cache.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Labelled.Ordering.Definitions.Abstract,
  RotationBST.Models.Labelled.Search.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Structures.WeightedSearch.Definitions.Abstract,
  RotationBST.Algorithms.MultipleTrees.Selection.Definitions.Abstract,
  RotationBST.Algorithms.MultipleTrees.Cache.Definitions.Abstract]
