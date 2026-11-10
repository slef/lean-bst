module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Tango.Algorithm.AbstractBridge

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

/-- **Tango trees are `O(log log n)`-competitive.** Some online BST algorithm,
fixed before any request is known, serves every request sequence from every
initial tree on `n` keys at total cost (one per request plus rotations) within
`O(log log n)` times the cost of any offline execution from the same tree, plus
`O(n log log n)` for initialization. It is Tango: a `Policy` run from the
balanced reference tree, after rotating the initial tree into it. -/
theorem exists_competitive (n : Nat) :
    ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      start.size = n → Execution start xs finish offline →
        (A.totalCost start xs : ℝ) ≤
          (56 * Real.logb 2 (Nat.log2 n + 1) + 16) * (offline + xs.length : Nat) +
            (14 * Real.logb 2 (Nat.log2 n + 1) + 6) * n :=
  Tango.exists_online_bound n

/-- **Tango with linear startup.** The same statement with startup `44n`
instead of `O(n log log n)`, at a larger coefficient. The algorithm runs the
bottom-up policy (`Tango.BottomUp`), which pays for first preference settings
from local credit, at most `42n` on the balanced reference; reaching the
reference from another initial tree costs at most `2n` more. -/
theorem exists_competitive_linear (n : Nat) :
    ∃ A : Algorithm, ∀ {start finish : Tree} {xs : List Nat} {offline : Nat},
      start.size = n → Execution start xs finish offline →
        (A.totalCost start xs : ℝ) ≤
          (70 * Real.logb 2 (Nat.log2 n + 1) + 20) * (offline + xs.length : Nat) + 44 * n :=
  Tango.exists_online_linear_bound n

end RotationBST.Tango.Algorithm.Results

/-- info: abstract audit passed for `RotationBST.Tango.Algorithm.Results`: 7 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Tango.Algorithm.Results allowing [
  RotationBST.Models.Rotation.Abstract, RotationBST.Models.Online.Abstract,
  RotationBST.Algorithms.Tango.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Tango.Reference.Abstract,
  RotationBST.Algorithms.Tango.State.Abstract, RotationBST.Algorithms.Tango.Preferences.Updates.Abstract,
  RotationBST.Bounds.Interleave.Definitions.Abstract, RotationBST.Algorithms.Tango.Definitions.Abstract, RotationBST.Algorithms.Tango.Paths.Abstract,
  RotationBST.Bounds.Interleave.Wilber.Abstract,
  RotationBST.Models.Region.Abstract, RotationBST.Algorithms.Tango.Auxiliary.Definitions.Abstract,
  RotationBST.Models.Pointer.Lazy.Skeleton.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract, RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Potential.Abstract]
