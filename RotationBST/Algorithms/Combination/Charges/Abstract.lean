module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Combination.Charges.AbstractBridge

@[expose] public section
namespace RotationBST.Combo.Charges.Results

theorem lazyFinger_nonneg (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) :
    0 ≤ lazyFinger factor t xs i :=
  RotationBST.Combo.Charges.lazyFinger_nonneg factor t xs i

theorem lazyFinger_mass (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.mass (fun _ => lazyFinger factor t) side xs lo hi =
      factor * ((LazyFinger.cost t (xs.take hi) : ℝ) - LazyFinger.cost t (xs.take lo)) :=
  RotationBST.Combo.Charges.lazyFinger_mass factor t side xs lo hi ordered

theorem lazyFinger_total (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat) :
    Analysis.total (fun _ => lazyFinger factor t) side xs = factor * LazyFinger.cost t xs :=
  RotationBST.Combo.Charges.lazyFinger_total factor t side xs

theorem lazyFinger_stable (factor overhead : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) (valid : ∀ x ∈ xs, x < t.size)
    (paid : factor * t.size ≤ overhead) :
    Analysis.total (fun _ => lazyFinger factor t) side (Analysis.segment xs lo hi) + overhead ≤
      Analysis.mass (fun _ => lazyFinger factor t) side xs lo hi + 2 * overhead :=
  RotationBST.Combo.Charges.lazyFinger_stable factor overhead t side xs lo hi ordered valid paid

theorem interleave_nonneg (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) :
    0 ≤ interleave factor t xs i :=
  RotationBST.Combo.Charges.interleave_nonneg factor t xs i

theorem interleave_mass (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.mass (fun _ => interleave factor t) side xs lo hi =
      factor * ((hi - lo : Nat) + (Wilber.interleave t (xs.take hi) : ℝ) - Wilber.interleave t (xs.take lo)) :=
  RotationBST.Combo.Charges.interleave_mass factor t side xs lo hi ordered

theorem interleave_total (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat) :
    Analysis.total (fun _ => interleave factor t) side xs = factor * (xs.length + Wilber.interleave t xs : Nat) :=
  RotationBST.Combo.Charges.interleave_total factor t side xs

theorem interleave_stable (factor : Nat) (t : Tree) (side : Bool) (xs : List Nat)
    (lo hi : Nat) (ordered : lo ≤ hi) :
    Analysis.total (fun _ => interleave factor t) side (Analysis.segment xs lo hi) ≤
      Analysis.mass (fun _ => interleave factor t) side xs lo hi :=
  RotationBST.Combo.Charges.interleave_stable factor t side xs lo hi ordered

theorem interleave_comparator (factor : Nat) (reference : Tree) {s t : Tree} {xs : List Nat} {k : Nat}
    (same : reference.size = s.size) (execution : RotationBST.Execution s xs t k) :
    Analysis.total (fun _ => interleave factor reference) false xs ≤
      (4 * factor : Nat) * (xs.length + k : Nat) :=
  RotationBST.Combo.Charges.interleave_comparator factor reference same execution

end RotationBST.Combo.Charges.Results

/-- info: abstract audit passed for `RotationBST.Combo.Charges.Results`: 9 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Combo.Charges.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Bounds.LazyFinger.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract,
  RotationBST.Algorithms.Combination.Charges.Definitions.Abstract]
