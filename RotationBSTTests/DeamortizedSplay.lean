module

public import RotationBST.Algorithms.Splay.Deamortization.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.Tests.DeamortizedSplay
open Deamortization

private def leaf : Tree := .node .nil .nil

-- Setup is separate: no empty input can hide instructions or response costs
-- in the per-request accounting, for any source and any certified program.
example {source : RotationBST.Algorithm} {saved : Tree}
    (d : Algorithm.Implementation source saved) :
    ∃ out, d.program [] = some out ∧ out.costs = [] ∧ out.instructions = [] := by
  obtain ⟨out, completed, _, _, _, length, total, _, _⟩ := d.correct [] (by simp)
  have costs : out.costs = [] := List.eq_nil_of_length_eq_zero length
  have instructions : out.instructions = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa only [costs, List.sum_nil, List.length_nil, Nat.zero_add] using total.symm
  exact ⟨out, completed, costs, instructions⟩

-- Splay performs no rotations on repeated root hits. Normalization must
-- nevertheless charge all three requests, even on the smallest universe.
example : Splay.algorithm.cost leaf [0, 0, 0] = 0 ∧
    Splay.algorithm.totalCost leaf [0, 0, 0] = 3 := by
  decide +kernel

example : ∃ d : Algorithm.Implementation Splay.algorithm leaf,
    ∃ out first, d.program [0, 0, 0] = some out ∧ d.program [0] = some first ∧
      out.costs.length = 3 ∧ 3 ≤ out.costs.sum ∧ out.costs.sum ≤ 238080 ∧
      first.costs.length = 1 ∧ first.instructions <+: out.instructions ∧
      first.costs <+: out.costs ∧ ∀ cost ∈ out.costs, cost < 251 := by
  obtain ⟨d⟩ := Splay.Deamortization.Results.implementation_exists leaf (by decide +kernel)
  have valid : ∀ x ∈ [0, 0, 0], x < leaf.size := by
    intro x member
    simp at member
    subst x
    decide +kernel
  obtain ⟨out, completed, _, _, _, length, total, bound, worst⟩ := d.correct [0, 0, 0] valid
  obtain ⟨first, prefixCompleted, instructions, costs⟩ := d.causal [0] [0, 0] out completed
  obtain ⟨one, oneCompleted, _, _, _, oneLength, _⟩ := d.correct [0]
    (by intro x member; simp at member; subst x; decide +kernel)
  have same := Option.some.inj (prefixCompleted.symm.trans oneCompleted)
  subst one
  have source : Splay.algorithm.totalCost leaf [0, 0, 0] = 3 := by decide +kernel
  rw [source] at bound
  have lower : 3 ≤ out.costs.sum := by
    simp only [List.length_cons, List.length_nil] at total
    omega
  refine ⟨d, out, first, completed, prefixCompleted, length, lower,
    bound, oneLength, instructions, costs, ?_⟩
  intro cost member
  have bound := worst cost member
  norm_num [leaf, Tree.size] at bound
  exact_mod_cast bound

-- One program and one completed scan work simultaneously against every
-- static tree and finger chosen afterwards. The scan covers the universe.
example (saved : Tree) (nonempty : saved ≠ .nil) :
    ∃ d : Algorithm.Implementation Splay.algorithm saved,
      ∃ out, d.program (List.range saved.size) = some out ∧
        d.startup + out.costs.sum ≤ 1111056 * saved.size ∧
        (∀ reference : Tree, saved.size = reference.size →
          (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
            952320 * (StaticTree.cost reference (List.range saved.size) : ℝ)) ∧
        (∀ finger : Nat, (d.startup + out.costs.sum : ℝ) ≤ 16 * saved.size +
          952320 * Bounds.fingerCost finger (List.range saved.size)) := by
  obtain ⟨d⟩ := Splay.Deamortization.Results.implementation_exists saved nonempty
  have valid : ∀ x ∈ List.range saved.size, x < saved.size := by
    intro x member
    exact List.mem_range.mp member
  have covers : ∀ x < saved.size, x ∈ List.range saved.size := by
    intro x member
    exact List.mem_range.mpr member
  obtain ⟨out, completed, _⟩ := d.correct (List.range saved.size) valid
  refine ⟨d, out, completed, Splay.Deamortization.Results.scanning d completed, ?_, ?_⟩
  · intro reference same
    exact Splay.Deamortization.Results.static_optimality d reference same valid covers completed
  · intro finger
    exact Splay.Deamortization.Results.static_finger d finger valid covers completed

end RotationBST.Tests.DeamortizedSplay
