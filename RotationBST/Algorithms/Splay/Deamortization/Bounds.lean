module

public import RotationBST.Algorithms.Deamortization.Algorithm.Abstract
public import RotationBST.Algorithms.Splay.Balance.Abstract
public import RotationBST.Algorithms.Splay.WorkingSet.Abstract
public import RotationBST.Algorithms.Splay.Scanning.Abstract
public import RotationBST.Algorithms.Splay.StaticOptimality.Abstract
public import RotationBST.Algorithms.Splay.StaticFinger.Abstract
import RotationBST.Bounds.Normalization.Proofs
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Splay.Deamortization
open RotationBST.Deamortization

/-- One deamortized splay program inherits every source bound below. -/
theorem implementation_exists (saved : Tree) (nonempty : saved ≠ .nil) :
    Nonempty (Algorithm.Implementation Splay.algorithm saved) :=
  Algorithm.Results.implementation_exists Splay.algorithm saved nonempty

theorem scanning {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {out : Scheduler.Output} (completed : d.program (List.range saved.size) = some out) :
    d.startup + out.costs.sum ≤ 1111056 * saved.size := by
  have bound := Algorithm.Results.total_bound d (by intro x member; exact List.mem_range.mp member) completed
  have source := Splay.Results.scanning saved
  omega

theorem balance {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 79360 *
      (xs.length * (2 + 3 * Real.logb 2 saved.size) + saved.size * Real.logb 2 saved.size) :=
  Algorithm.Results.transfer d valid completed (Splay.Results.balance saved xs valid)

theorem working_set {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    d.startup + out.costs.sum ≤ 16 * saved.size + 79360 *
      (11 * workingSetSum saved.size [] xs + 6 * saved.size * (1 + saved.size.log2)) := by
  have bound := Algorithm.Results.total_bound d valid completed
  have source := Splay.Results.workingSet saved xs valid
  have requests := BoundsBridge.length_le_workingSetSum saved.size [] xs
  unfold RotationBST.Algorithm.totalCost at bound
  omega

/-- The reference tree is chosen after the physical program; coverage is the
same hypothesis as the source static-optimality theorem. -/
theorem static_optimality {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    (reference : Tree) (same : saved.size = reference.size) {xs : List Nat}
    (valid : ∀ x ∈ xs, x < saved.size) (covers : ∀ x < saved.size, x ∈ xs)
    {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 952320 * (StaticTree.cost reference xs : ℝ) := by
  have bound := Algorithm.Results.transfer d valid completed (Splay.Results.staticOptimality_fixedTree saved reference xs same valid covers)
  linarith

theorem static_finger {saved : Tree} (d : Algorithm.Implementation Splay.algorithm saved)
    (finger : Nat) {xs : List Nat} (valid : ∀ x ∈ xs, x < saved.size)
    (covers : ∀ x < saved.size, x ∈ xs) {out : Scheduler.Output} (completed : d.program xs = some out) :
    (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size + 952320 * Bounds.fingerCost finger xs := by
  have bound := Algorithm.Results.transfer d valid completed (Splay.Results.staticFinger_all_accessed saved xs finger valid covers)
  linarith

/-- Without coverage, retain the source's initialization allowance. The same
constants work for all saved trees and all certified transformed programs. -/
theorem static_optimality_general :
    ∃ C D : Nat, ∀ saved : Tree, ∀ d : Algorithm.Implementation Splay.algorithm saved,
      ∀ xs : List Nat, (∀ x ∈ xs, x < saved.size) → ∀ out,
        d.program xs = some out →
        (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
          C * Bounds.staticCost saved.size xs + D * saved.size * (1 + (saved.size.log2 : ℝ)) := by
  obtain ⟨C, D, sourceBound⟩ := Splay.Results.staticOptimality
  refine ⟨79360 * C, 79360 * D, ?_⟩
  intro saved d xs valid out completed
  have bound := Algorithm.Results.transfer d valid completed (sourceBound saved xs valid)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

/-- A fixed finger need not occur, and other stored keys may remain unused.
The retained allowance is the source's `n(1 + floor(log₂ n))` term. -/
theorem static_finger_general :
    ∃ C D : Nat, ∀ saved : Tree, ∀ d : Algorithm.Implementation Splay.algorithm saved,
      ∀ (xs : List Nat) (finger : Nat), finger < saved.size →
        (∀ x ∈ xs, x < saved.size) → ∀ out, d.program xs = some out →
        (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
          C * Bounds.fingerCost finger xs + D * saved.size * (1 + (saved.size.log2 : ℝ)) := by
  obtain ⟨C, D, sourceBound⟩ := Splay.Results.staticFinger
  refine ⟨79360 * C, 79360 * D, ?_⟩
  intro saved d xs finger fingerValid valid out completed
  have bound := Algorithm.Results.transfer d valid completed (sourceBound saved xs finger fingerValid valid)
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  nlinarith

end RotationBST.Splay.Deamortization
