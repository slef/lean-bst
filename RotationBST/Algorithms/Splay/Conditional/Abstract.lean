module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Conditional.AbstractBridge

@[expose] public section

/-! The long-splay theorem. The variant and its threshold are spelled out in
`Conditional/Algorithm/Abstract`. These bounds count only restructuring;
short searches still navigate to their keys in the pointer model. -/
namespace RotationBST.Splay.Results

theorem long_splay (w : Nat → ℝ) (positive : ∀ i, 0 < w i)
    (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((conditionalRun w t xs).2 : ℝ) ≤
      2 * ∑ i ∈ Finset.range t.size, Real.logb 2 (mass w t 0 / w i) :=
  Splay.long_splay w positive t xs valid

theorem long_splay_unit (t : Tree) (xs : List Nat) (valid : ∀ x ∈ xs, x < t.size) :
    ((conditionalRun (fun _ => 1) t xs).2 : ℝ) ≤ 2 * (t.size : ℝ) * Real.logb 2 t.size :=
  Splay.long_splay_unit t xs valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract,
  RotationBST.Algorithms.Splay.Conditional.Algorithm.Abstract]
