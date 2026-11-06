module

import RotationBST.Audit.Check
public import RotationBST.Algorithms.Splay.Deamortization.AbstractBridge

@[expose] public section

/-! Splay bounds for the same deamortized program. Setup is charged once;
sharper static comparisons retain coverage; general versions retain startup.
This is an abstract BST cost theorem, not a finite-storage implementation. -/
namespace RotationBST.Splay.Deamortization.Results
open RotationBST.Deamortization

theorem implementation_exists (saved : Tree) (nonempty : saved ≠ .nil) :
    Nonempty (Algorithm.Implementation Splay.algorithm saved) :=
  RotationBST.Splay.Deamortization.implementation_exists saved nonempty

theorem scanning {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {out : Scheduler.Output} (completed : d.program (List.range saved.size) = some out) :
    d.startup + out.costs.sum ≤ 1111056 * saved.size :=
  RotationBST.Splay.Deamortization.scanning d completed

theorem balance {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 79360 *
      (xs.length * (2 + 3 * Real.logb 2 saved.size) + saved.size * Real.logb 2 saved.size) :=
  RotationBST.Splay.Deamortization.balance d valid completed

theorem working_set {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 79360 *
      (11 * workingSetSum saved.size [] xs + 6 * saved.size * (1 + saved.size.log2)) :=
  RotationBST.Splay.Deamortization.working_set d valid completed

theorem static_optimality {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    (reference : Tree) (same : saved.size = reference.size) {xs : List Nat}
    (valid : ∀ x ∈ xs, x < saved.size) (covers : ∀ x < saved.size, x ∈ xs)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 952320 * (StaticTree.cost reference xs : ℝ) :=
  RotationBST.Splay.Deamortization.static_optimality d reference same valid covers completed

theorem static_finger {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    (finger : Nat) {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    (covers : ∀ x < saved.size, x ∈ xs) {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 952320 * Bounds.fingerCost finger xs :=
  RotationBST.Splay.Deamortization.static_finger d finger valid covers completed

theorem static_optimality_general :
    ∃ C D : Nat, ∀ saved : Tree, ∀ d : Algorithm.Implementation Splay.algorithm saved,
      ∀ xs : List Nat, (∀ x ∈ xs, x < saved.size) → ∀ out,
        d.program xs = some out →
        (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
          C * Bounds.staticCost saved.size xs + D * saved.size * (1 + (saved.size.log2 : ℝ)) :=
  RotationBST.Splay.Deamortization.static_optimality_general

theorem static_finger_general :
    ∃ C D : Nat, ∀ saved : Tree, ∀ d : Algorithm.Implementation Splay.algorithm saved,
      ∀ (xs : List Nat) (finger : Nat), finger < saved.size →
        (∀ x ∈ xs, x < saved.size) → ∀ out, d.program xs = some out →
        (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
          C * Bounds.fingerCost finger xs + D * saved.size * (1 + (saved.size.log2 : ℝ)) :=
  RotationBST.Splay.Deamortization.static_finger_general

end RotationBST.Splay.Deamortization.Results

/-- info: abstract audit passed for `RotationBST.Splay.Deamortization.Results`: 8 root declarations -/
#guard_msgs in
#check_bst_abstract RotationBST.Splay.Deamortization.Results allowing [
  RotationBST.Models.Rotation.Abstract,
  RotationBST.Models.Online.Abstract,
  RotationBST.Models.Pointer.Machine.Abstract,
  RotationBST.Models.Multifinger.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Definitions.Abstract,
  RotationBST.Models.Multifinger.Program.Replay.Definitions.Abstract,
  RotationBST.Bounds.StaticTree.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Scheduler.Definitions.Abstract,
  RotationBST.Algorithms.Deamortization.Algorithm.Definitions.Abstract,
  RotationBST.Algorithms.Splay.Algorithm.Abstract,
  RotationBST.Algorithms.Splay.Online.Abstract,
  RotationBST.Bounds.Abstract,
  RotationBST.Bounds.WorkingSet.Abstract]
