module

public import RotationBST.Splay.Algorithm.Abstract
public import RotationBST.Bounds.Abstract

@[expose] public section

/-! Finite-sum probability model for the snapshot theorem. Requests are independent,
with fixed probabilities `p x` on `0, …, n-1`. No measure-theory conventions are hidden
in the statement: the expectations below are explicit finite sums. -/
namespace RotationBST.Splay

/-- Mean static search cost in this tree, including one unit for the request.
Splay's rotation count equals the ordinary search depth. -/
noncomputable def meanSearch (n : Nat) (p : Nat → ℝ) (t : Tree) : ℝ :=
  1 + ∑ x ∈ Finset.range n, p x * (run t x).2

/-- Expected static search cost of the tree after exactly `j` independent accesses. -/
noncomputable def snapshotAt (n : Nat) (p : Nat → ℝ) (t : Tree) : Nat → ℝ
  | 0 => meanSearch n p t
  | j + 1 => ∑ x ∈ Finset.range n, p x * snapshotAt n p (run t x).1 j

/-- Stop uniformly before one of the first `m` accesses; inspect the static tree. -/
noncomputable def snapshotMean (n : Nat) (p : Nat → ℝ) (t : Tree) (m : Nat) : ℝ :=
  (∑ j ∈ Finset.range m, snapshotAt n p t j) / m

/-- Shannon entropy in bits; zero-probability terms are zero. -/
noncomputable def probabilityEntropy (n : Nat) (p : Nat → ℝ) : ℝ :=
  ∑ x ∈ Finset.range n, p x * Real.logb 2 (1 / p x)

end RotationBST.Splay
