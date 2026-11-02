module

import RotationBST.AbstractAudit.Check
public import RotationBST.Tango.Algorithm.Balanced
public import RotationBST.Tango.Reference.Results.Abstract

@[expose] public section
namespace RotationBST.Tango.Algorithm.Results

/-- A fixed executable causal policy exists for every reference tree. -/
theorem policy_exists (reference : Tree) : Nonempty (Policy reference) := ⟨policy reference⟩

/-- Every requested rank is actually accessed, and the final marking realizes
the canonical preferred paths and nesting. -/
theorem execution {reference : Tree} (p : Policy reference) (xs : List Nat)
    (valid : ∀ x ∈ xs, x < reference.size) :
    Execution reference xs (p.run xs).1.tree (p.run xs).2 ∧
      MarkedTree.Maintains (p.run xs).1 reference xs :=
  ⟨(p.run_spec xs valid).1, (p.run_spec xs valid).2.1⟩

/-- The policy is fixed independently of the offline comparator and its request
sequence. Cost includes one unit per request, with a separate initialization term. -/
theorem competitive {reference : Tree} (p : Policy reference)
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : reference.size = start.size) (comparator : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 (height reference) + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 (height reference) + 4) * reference.size :=
  p.competitive_bound size comparator

/-- On `2^h - 1` keys the factor is logarithmic in `h`. -/
theorem perfect_competitive (h : Nat) (p : Policy (perfect h))
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : (perfect h).size = start.size) (comparator : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 h + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 h + 4) * (2 ^ h - 1 : Nat) :=
  p.perfect_competitive_bound h size comparator

/-- The doubly logarithmic coefficient holds for every universe size, using an
executable balanced reference tree with exactly `n` keys. -/
theorem balanced_competitive (n : Nat) (p : Policy (balanced n))
    {start finish : Tree} {xs : List Nat} {offline : Nat}
    (size : start.size = n) (comparator : Execution start xs finish offline) :
    ((p.run xs).2 : ℝ) + xs.length ≤
      (56 * Real.logb 2 (Nat.log2 n + 1) + 16) * (offline + xs.length : Nat) +
        (14 * Real.logb 2 (Nat.log2 n + 1) + 4) * n :=
  p.balanced_competitive_bound n size comparator

end RotationBST.Tango.Algorithm.Results

#check_bst_abstract RotationBST.Tango.Algorithm.Results allowing [
  RotationBST.Model.Abstract, RotationBST.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Tango.Reference.Abstract,
  RotationBST.Tango.State.Definitions.Abstract, RotationBST.Tango.State.Nesting.Abstract,
  RotationBST.Tango.State.Canonical.Abstract, RotationBST.Tango.Preferences.Updates.Abstract,
  RotationBST.Tango.Definitions.Abstract, RotationBST.Tango.Paths.Abstract,
  RotationBST.Tango.Wilber.Abstract, RotationBST.Tango.Transition.Abstract,
  RotationBST.Arboral.Treap.Regions.Abstract, RotationBST.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Pointer.Lazy.Skeleton.Abstract, RotationBST.Pointer.Traces,
  RotationBST.Pointer.Machine.Abstract, RotationBST.Splay.Algorithm.Abstract,
  RotationBST.Splay.Potential.Abstract]
