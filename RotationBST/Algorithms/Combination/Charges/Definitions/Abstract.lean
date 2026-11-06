module

public import RotationBST.Algorithms.Combination.Analysis.Definitions.Abstract
public import RotationBST.Bounds.LazyFinger.Definitions.Abstract
public import RotationBST.Bounds.Interleave.Definitions.Abstract

@[expose] public section
namespace RotationBST.Combo.Charges

/-- The actual cost increments of a fixed lazy-finger tree. Taking real
prefix differences makes contiguous sums telescope; monotonicity proves
nonnegativity. The scale absorbs the source-algorithm simulation constant. -/
noncomputable def lazyFinger (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) : ℝ :=
  factor * ((LazyFinger.cost t (xs.take (i + 1)) : ℝ) - LazyFinger.cost t (xs.take i))

/-- Normalized Wilber increments, with one unit per request. A contiguous
window retains every switch internal to that window. -/
noncomputable def interleave (factor : Nat) (t : Tree) (xs : List Nat) (i : Nat) : ℝ :=
  factor * (1 + (Wilber.interleave t (xs.take (i + 1)) : ℝ) - Wilber.interleave t (xs.take i))

end RotationBST.Combo.Charges
