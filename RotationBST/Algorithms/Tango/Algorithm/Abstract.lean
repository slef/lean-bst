module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.Balanced
public import RotationBST.Algorithms.Tango.Reference.Results

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
  RotationBST.Models.Rotation.Abstract, RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.State.Defs, RotationBST.Algorithms.Tango.State.Nesting.Defs,
  RotationBST.Algorithms.Tango.State.Canonical.Defs, RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract, RotationBST.Bounds.Interleave.Transition.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract, RotationBST.Models.Pointer.Traces,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
