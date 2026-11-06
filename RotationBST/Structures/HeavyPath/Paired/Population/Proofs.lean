module

public import RotationBST.Structures.HeavyPath.Paired.Exposure.Definitions.Abstract
public import RotationBST.Structures.PopTart.Chocolate.Abstract
public import RotationBST.Models.Pointer.Mirror.Abstract
import Mathlib.Tactic

@[expose] public section
namespace RotationBST.HeavyPath.Paired.Population
open PopTart PopTart.Chocolate LabelledCursor

/-- Opaque payloads may add keys but never remove the separators counted by
the original fringe population. -/
theorem leaf_count_size (t : WeightedTree) : 1 ≤ t.leafCount ∧ t.leafCount ≤ t.tree.size + 1 := by
  induction t with
  | leaf payload weight => simp [WeightedTree.leafCount, WeightedTree.tree, WeightedTree.skeleton]
  | node l r ihL ihR =>
    change 1 ≤ l.leafCount + r.leafCount ∧
      l.leafCount + r.leafCount ≤ l.tree.size + 1 + r.tree.size + 1
    omega

/-- Each stack's fringe population is bounded by the whole paired tree,
including its endpoint separator and arbitrarily large opaque payloads. -/
theorem pair_population (p : Stacks) :
    1 ≤ p.lower.decode.leafCount ∧ p.lower.decode.leafCount ≤ p.tree.size ∧
    1 ≤ p.upper.decode.leafCount ∧ p.upper.decode.leafCount ≤ p.tree.size := by
  have lower := leaf_count_size p.lower.decode
  have upper := leaf_count_size p.upper.decode
  simp only [Stacks.tree, Tree.size, Tree.mirror_size]
  omega

private theorem lower_log {p : Stacks} {n : Nat} (size : p.tree.size ≤ n) :
    Real.logb 2 (p.lower.decode.leafCount) ≤ Real.logb 2 n := by
  have population := pair_population p
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast (show 0 < p.lower.decode.leafCount by omega)
  · exact_mod_cast population.2.1.trans size

private theorem upper_log {p : Stacks} {n : Nat} (size : p.tree.size ≤ n) :
    Real.logb 2 (p.upper.decode.leafCount) ≤ Real.logb 2 n := by
  have population := pair_population p
  apply Real.logb_le_logb_of_le (by norm_num)
  · exact_mod_cast (show 0 < p.upper.decode.leafCount by omega)
  · exact_mod_cast population.2.2.2.trans size

/-- A paired push, including the caller's descent, has logarithmic physical
cost in any enclosing tree-size bound, independently of analysis weights. -/
theorem push_cost_bound {α : Type} {p : Stacks} (valid : p.Valid) (frame : Frame α)
    {n : Nat} (size : p.tree.size ≤ n) :
    (p.pushCost frame + 1 : ℝ) ≤ 10 + 14 * Real.logb 2 n := by
  cases frame with
  | left key payload =>
    have worst := Chocolate.Results.push_worst_case valid.2
    have logarithm := upper_log size
    simp only [Stacks.pushCost, Nat.cast_add, Nat.cast_ofNat]
    linarith
  | right payload key =>
    have worst := Chocolate.Results.push_worst_case valid.1
    have logarithm := lower_log size
    simp only [Stacks.pushCost, Nat.cast_add, Nat.cast_ofNat]
    linarith

/-- Exposure includes entering the stack, popping, returning, and rotating
the source ancestor to the root. -/
theorem expose_cost_bound {α : Type} {p : Stacks} (valid : p.Valid) (frame : Frame α)
    {n : Nat} (size : p.tree.size ≤ n) :
    (p.exposeCost frame : ℝ) ≤ 10 + 10 * Real.logb 2 n := by
  cases frame with
  | left key payload =>
    have worst := Chocolate.Results.pop_worst_case valid.2
    have logarithm := upper_log size
    simp only [Stacks.exposeCost, Nat.cast_add, Nat.cast_ofNat]
    linarith
  | right payload key =>
    have worst := Chocolate.Results.pop_worst_case valid.1
    have logarithm := lower_log size
    simp only [Stacks.exposeCost, Nat.cast_add, Nat.cast_ofNat]
    linarith

end RotationBST.HeavyPath.Paired.Population
