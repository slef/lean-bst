module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.AccessLemma.AbstractBridge

@[expose] public section

/-! The analysis weights and potential are defined in `Algorithms/Splay/Potential/Abstract`.
Weights are ghost data: the algorithm does not inspect or maintain them. -/
namespace RotationBST.Splay.Results

/-- Weighted access lemma, using the accessed node's own weight. -/
theorem access_lemma (w : Nat → ℝ) (positive : ∀ i, 0 < w i)
    (t : Tree) (x : Nat) (valid : x < t.size) :
    ((run t x).2 : ℝ) + potential w (run t x).1 0 - potential w t 0 ≤
      3 * (Real.logb 2 (mass w t 0) - Real.logb 2 (w x)) + 1 :=
  Splay.access_lemma w positive t x valid

/-- Stronger original form: the denominator is the initial subtree mass of
 the accessed node, not merely its own weight. -/
theorem access_lemma_subtree (w : Nat → ℝ) (positive : ∀ i, 0 < w i)
    (t : Tree) (x : Nat) (valid : x < t.size) :
    ((run t x).2 : ℝ) + potential w (run t x).1 0 - potential w t 0 ≤
      3 * (Real.logb 2 (mass w t 0) -
        Real.logb 2 (mass w (locate t x).focus (Pointer.offset (locate t x).context))) + 1 :=
  Splay.access_lemma_subtree w positive t x valid

end RotationBST.Splay.Results

-- Explicit reading boundary; proof bodies remain behind the bridge.
/-- info: abstract audit passed for `RotationBST.Splay.Results`: 2 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
